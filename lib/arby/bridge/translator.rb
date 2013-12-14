require 'alloy/bridge/imports'
require 'alloy/ast/instance'
require 'alloy/ast/tuple_set'
require 'alloy/ast/types'

module Alloy
  module Bridge

    module Translator
      include Utils
      extend self

      # Takes an instance of Alloy::Ast::Instance parametrized with
      # Alloy::Bridge::Atom, and Alloy::Bridge::TupleSet, and converts
      # it to an instance of the same class parametrized with
      # Alloy::Ast::Sig, and Alloy::Ast::TupleSet.  Additionally, it
      # populates the field values of the newly created atoms
      # according to field values in +inst+.
      #
      # @param inst [Alloy::Ast::Instance<Alloy::Bridge::Atom, Alloy::Bridge::TupleSet>]
      # @return [Alloy::Ast::Instance<Alloy::Ast::Sig, Alloy::Ast::TupleSet>]
      def to_arby_instance(inst)
        atoms   = inst.atoms.map{|a| _create_atom(a)}
        tmpi    = Alloy::Ast::Instance.new atoms
        flds    = inst.fields.map{|name| [name, _to_tuple_set(tmpi, inst.field(name))]}
        skolems = inst.skolems.map{|name| [name, _to_tuple_set(tmpi, inst.skolem(name))]}

        fld_map    = Hash[flds]
        skolem_map = Hash[skolems]

        # restore field values
        atoms.each do |atom|
          atom.meta.fields(false).each do |fld|
            # select those tuples in +fld+s relation that have +atom+ on the lhs
            fld_tuples = fld_map[fld.name].select{|tuple| tuple[0] == atom}
            # strip the lhs
            fld_val = fld_tuples.map{|tuple| tuple[1..-1]}
            # write that field value
            atom.write_field(fld, fld_val)
          end
        end

        Alloy::Ast::Instance.new atoms, fld_map, skolem_map, false
      end

      private

      SIG_PREFIX = "this/"

      # @param atom [Alloy::Bridge::Atom]
      # @return [Alloy::Ast::Sig]
      def _create_atom(atom)
        sig_cls = _type_to_sig!(atom.type)
        a = sig_cls.new()
        a.label = atom.label
        a
      end

      def _type_to_atype(type)
        Alloy::Ast::AType.get type.prim_sigs.map{ |a4prim_sig|
          prim_sig_name = a4prim_sig.toString
          sig_cls = _type_to_sig(nil, prim_sig_name)
          (sig_cls ? sig_cls : Alloy::Ast::AType.builtin(prim_sig_name)) or break nil
        }, false
      end

      def _type_to_sig(type, type_name=nil)
        return nil if type and type.arity != 1
        sig_name = type ? type.signature : type_name
        sig_name = sig_name[SIG_PREFIX.size..-1] if sig_name.start_with?(SIG_PREFIX)
        Alloy.meta.find_sig(sig_name)
      end

      def _type_to_atype!(type) _type_to_atype(type) or fail("type #{type} not found") end
      def _type_to_sig!(type)   _type_to_sig(type) or fail("sig #{type} not found") end

      # @param inst [Alloy::Ast::Instance<Alloy::Ast::Sig, Alloy::Ast::TupleSet>]
      # @param ts [Alloy::Bridge::TupleSet]
      def _to_tuple_set(inst, ts)
        tuples = ts.tuples.map do |tuple|
          atoms = tuple.map{|a| inst.atom!(a.label)}
          # type = tuple.map{|a| _a4type_to_atype!(a.a4type)}
          # Tuple.wrap(value, Alloy::Ast::AType.get(type))
        end
        type = _type_to_atype!(ts.type)
        Alloy::Ast::TupleSet.wrap(tuples, type)
      end

    end
  end
end
