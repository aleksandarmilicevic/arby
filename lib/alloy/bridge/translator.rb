require 'alloy/bridge/imports'
require 'alloy/ast/instance'

module Alloy
  module Bridge

    class Atom
      attr_reader :name, :a4type
      def initialize(name, a4type) @name, @a4type = name, a4type end
      def to_s()                   "#{name}: #{a4type.toString}" end
    end

    module Translator
      extend self

      SIG_PREFIX = "this/"

      # Takes an Rjb Proxy object pointing to an A4Solution, gets all
      # atoms from it, and converts them to instances of
      # corresponding aRby sig classes.
      #
      # @param a4atoms [Rjb::Proxy -> A4Solution]
      # @return [Array(Sig)]
      def translate_atoms(a4sol)
        a4atoms = a4sol.getAllAtoms
        len = a4atoms.size
        (0...len).map do |idx|
          translate_atom(a4atoms.get(idx))
        end
      end

      # Takes an Rjb Proxy object pointing to an alloy atom, and
      # converts it to an instance of the corresponding aRby sig
      # class.
      #
      # @param a4atom [Rjb::Proxy -> ExprVar]
      # @return [Sig]
      def translate_atom(a4atom)
        sig_name = a4atom.type.toExpr.toString
        sig_name = sig_name[SIG_PREFIX.size..-1] if sig_name.start_with?(SIG_PREFIX)
        sig_cls = Alloy.meta.find_sig(sig_name)
        fail "sig #{sig_name} not found" unless sig_cls
        atom = sig_cls.new()
        atom.label = a4atom.toString
        atom
      end

      # Returns a hash of tuples grouped by field names.
      #
      # @param a4tuple_set [Rjb::Proxy ~> A4TupleSet]
      # @return [Array(Tuple)], where Tuple is Array(Atom)
      def translate_tuple_set(a4tuple_set)
        a4iterator = a4tuple_set.iterator
        tuples = []
        while a4iterator.hasNext
          t = a4iterator.next
          tuples << (0...t.arity).map{|col| Atom.new(t.atom(col), t.sig(col)) }
        end
        tuples
      end

      # Returns a hash of tuples grouped by field names.
      #
      # @param a4world [Rjb::Proxy ~> CompModule]
      # @param a4sol [Rjb::Proxy ~> A4Solution]
      # @return [Alloy::Ast::Instance]
      def to_instance(a4world, a4sol)
        atoms = translate_atoms(a4sol)

        fld_map = Compiler.all_fields(a4world).map do |field|
          [field.label, translate_tuple_set(a4sol.eval(field))]
        end
        fld_map = Hash[fld_map]

        skolem_map = jmap(a4sol.getAllSkolems) do |expr|
          a4_tuple_set = a4sol.eval(expr)
          [expr.toString, translate_tuple_set(a4sol.eval(expr))]
        end
        skolem_map = Hash[skolem_map]

        Alloy::Ast::Instance.new(atoms, fld_map, skolem_map)
      end

      # Takes a map of relations to tuples, and a list of aRby atom
      # objects.  Populates the atoms' fields (instance variables) to
      # the values in +map+.  Returns a hash mapping atom labels to
      # atoms.
      #
      # @param a4world [Rjb::Proxy ~> CompModule]
      # @param a4sol [Rjb::Proxy ~> A4Solution]
      # @return [Alloy::Ast::Instance]
      def recreate_object_graph(a4world, a4sol)
        inst = to_instance(a4world, a4sol)

        inst.atoms.each do |atom|
          atom.meta.fields(false).each do |fld|
            # select those tuples in +fld+s relation that have +atom+ on the lhs
            fld_tuples = inst.field(fld.name).select{|tuple| tuple.first.name == atom.label}
            # strip the lhs and convert the rest to arby atoms to
            # obtain the field value for the +atom+ atom
            fld_val = fld_tuples.map{|tuple|
              tuple[1..-1].map{|a| inst.atom!(a.name)}
            }
            # write that field value
            atom.write_field(fld, fld_val)
          end
        end

        inst
      end

      # @param a4arr [Rjb::Proxy ~> Array]
      # @return [Array]
      def java_to_ruby_array(a4arr)
        size = a4arr.size
        (0...size).map{|i| a4arr.get(i)}
      end

      # @param a4arr [Rjb::Proxy ~> Array]
      def jmap(a4arr, &block)
        java_to_ruby_array(a4arr).map(&block)
      end

    end
  end
end
