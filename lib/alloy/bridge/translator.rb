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
      # @param a4world [Rjb::Proxy ~> CompModule]
      # @param a4sol [Rjb::Proxy ~> A4Solution]
      # @return [Hash(String, Array(Tuple))], where Tuple is Array(Atom)
      def field_tuples(a4world, a4sol)
        alloy_fields = Compiler.all_fields(a4world)
        map = alloy_fields.map do |field|
          fld_name = field.label
          a4_tuple_set = a4sol.eval(field)
          a4_iterator = a4_tuple_set.iterator
          fld_tuples = []
          while a4_iterator.hasNext
            t = a4_iterator.next
            fld_tuples << (0...t.arity).map{|col| Atom.new(t.atom(col), t.sig(col)) }
          end
          [fld_name, fld_tuples]
        end
        Hash[map]
      end


      # Takes a map of relations to tuples, and a list of aRby atom
      # objects.  Populates the atoms' fields (instance variables) to
      # the values in +map+.  Returns a hash mapping atom labels to
      # atoms.
      #
      # @param fld_map [Hash(String, Array(Tuple)], where Tuple is Array(Atom)
      #                                             - maps relation names
      #                                               to lists of tuples
      # @param atoms [Array(Sig)]
      # @return [Hash(String, Sig)]                 - maps atom labels to atoms
      def recreate_object_graph(a4world, a4sol)
        atoms = translate_atoms(a4sol)
        fld_map = field_tuples(a4world, a4sol)
        label2atom = Hash[atoms.map{|a| [a.label, a]}]

        atoms.each do |atom|
          atom.meta.fields(false).each do |fld|
            # select those tuples in +fld+s relation that have +atom+ on the lhs
            fld_tuples = fld_map[fld.name].select{|tuple| tuple.first.name == atom.label}
            # strip the lhs and convert the rest to arby atoms (by looking up in
            # the +label2atom+ hash) to obtain the field value for the +atom+ atom
            fld_val = fld_tuples.map{|tuple|
              tuple[1..-1].map{|a| label2atom[a.name]}
            }
            # write that field value
            atom.write_field(fld, fld_val)
          end
        end

        Alloy::Ast::Instance.new(atoms)
      end

      # def recreate_object_graph(map, atoms)
      #   label2atom = Hash[atoms.map{|a| [a.label, a]}]
      #   map.each do |key, value|
      #     for tuple in value
      #       lhs   = label2atom[tuple[0].name]
      #       rhs   = label2atom[tuple[1].name]
      #       field = lhs.meta.field(key)
      #       if field.scalar?
      #         lhs.write_field(field, rhs)
      #       else
      #         if !lhs.read_field(field)
      #           # the field is not a scalar, and this is the first
      #           # atom we are adding to this field
      #           lhs.write_field(field, [rhs])
      #         else
      #           lhs.write_field(field, lhs.read_field(field).push(rhs))
      #         end
      #       end
      #     end
      #   end
      #   label2atom
      # end

    end
  end
end
