require 'arby/bridge/imports'
require 'arby/ast/instance'
require 'arby/ast/tuple_set'
require 'arby/ast/types'

module Arby
  module Bridge

    module Translator
      include Utils
      extend self

      # Takes an instance of Arby::Ast::Instance parametrized with
      # Arby::Bridge::Atom, and Arby::Bridge::TupleSet, and converts
      # it to an instance of the same class parametrized with
      # Arby::Ast::Sig, and Arby::Ast::TupleSet.  Additionally, it
      # populates the field values of the newly created atoms
      # according to field values in +inst+.
      #
      # @param inst [Arby::Ast::Instance<Arby::Bridge::Atom, Arby::Bridge::TupleSet>]
      # @param univ [Arby::Ast::Universe]
      # @return [Arby::Ast::Instance<Arby::Ast::Sig, Arby::Ast::TupleSet>]
      def to_arby_instance(inst, univ=nil, compiler=nil)
        atoms = $sol_timer.time_it("atoms") {
          inst.atoms.map{|a| _get_atom(compiler, a, univ)}.compact
        }

        tmpi = Arby::Ast::Instance.new :atoms => atoms, :univ => univ

        flds = compiler.sigs.map{|s| s.meta.fields}.flatten.map{ |fld|
          fld_name = Arby.conf.alloy_printer.arg_namer[fld]
          ts = inst.field(fld_name) and [fld, _to_tuple_set(compiler, tmpi, ts)]
        }

        skolems = inst.skolems.map{ |name|
          [name, _to_tuple_set(compiler, tmpi, inst.skolem(name))]
        }

        fld_map    = Hash[flds.compact]
        skolem_map = Hash[skolems.compact]

        # restore field values
        atoms.select{|a| a.is_a?(Arby::Ast::ASig)}.each do |atom|
          atom.meta.pfields(false).each do |fld|
            # select those tuples in +fld+s relation that have +atom+ on the lhs
            fld_tuples = fld_map[fld].select{|tuple| tuple[0] == atom}
            # strip the lhs
            fld_val = fld_tuples.map{|tuple| tuple[1..-1]}
            # write that field value
            atom.write_field(fld, fld_val)
          end
        end

        Arby::Ast::Instance.new :atoms      => atoms,
                                :fld_map    => fld_map,
                                :skolem_map => skolem_map,
                                :dup        => false,
                                :univ       => univ,
                                :model      => compiler.model
      end

      private

      SIG_PREFIX = "this/"

      def _get_atom(compiler, atom, univ=nil)
        new_atom =
          (univ and univ.find_atom(atom.label)) ||
          (sig_cls = _this_type_to_sig!(compiler, atom.type) and sig_cls.new())
        if new_atom
          new_atom.__label = atom.label
          new_atom
        else
          atom
        end
      end

      def _type_to_atype(compiler, type)
        compiler.type2atype[type] ||= begin
          Arby::Ast::AType.get type.prim_sig_names.map{ |prim_sig_name|
            sig_cls = _type_to_sig(compiler, nil, prim_sig_name)
            (sig_cls ? sig_cls : Arby::Ast::AType.builtin(prim_sig_name)) or break nil
          }, false
        end
      end

      def _type_to_sig(compiler, type, type_name=nil)
        return nil if type and type.arity != 1
        sig_name = type ? type.signature : type_name
        compiler.type2sig[sig_name] ||= begin
          sig_name = sig_name[SIG_PREFIX.size..-1] if sig_name.start_with?(SIG_PREFIX)
          compiler.sigs.find{|s| Arby.conf.alloy_printer.sig_namer[s] == sig_name}
        end
      end

      def _type_to_atype!(*a) _type_to_atype(*a) or fail "type #{a[1]} not found" end
      def _type_to_sig!(*a)   _type_to_sig(*a) or fail "sig #{a[1]} not found" end
      def _this_type_to_sig!(compiler, type)
        if type.signature.start_with?(SIG_PREFIX)
          _type_to_sig!(compiler, type)
        else
          _type_to_sig(compiler, type)
        end
      end

      # @param inst [Arby::Ast::Instance<Arby::Ast::Sig, Arby::Ast::TupleSet>]
      # @param ts [Arby::Bridge::TupleSet]
      def _to_tuple_set(compiler, inst, ts)
        unary = true
        tuples = $sol_timer.time_it("tuplemap") {
          ts.tuples.map do |tuple|
            unary = unary && tuple.size == 1
            atoms = tuple.map{|a| inst.atom!(a.label)}
          end
        }
        if Arby.conf.wrap_field_values
          type =  $sol_timer.time_it("toatype") { _type_to_atype!(compiler, ts.type) }
          $sol_timer.time_it("wrap") {
            Arby::Ast::TupleSet.wrap(tuples, type)
          }
        else
          tuples
        end
      end

    end
  end
end
