require 'alloy/bridge/imports'
module Alloy
  module Bridge
    class Solution

      def initialize(a4sol, compiler=nil)
        @a4sol = a4sol
        @compiler = compiler
      end

      # @see Solution.all_atoms
      def all_atoms
        fail_if_no_solution
        self.class.all_atoms(@a4sol)
      end

      # @see Solution.field_tuples
      def field_tuples()
        fields = @compiler.all_fields
        self.class.field_tuples(fields, @a4sol)
      end

      private

      def fail_if_no_solution
        fail "no A4Solution given" unless @a4sol
      end

      # =================================================================
      # Static, functional-style API (no state carried around)
      # =================================================================
      class << self
        include Imports

        class Atom
          attr_reader :name, :a4type
          def initialize(name, a4type) @name, @a4type = name, a4type end
          def to_s()                   "#{name}: #{a4type.toString}" end
        end

        # Takes a proxy to an Alloy solution and extract a list of all
        # atoms from it.
        #
        # @param a4sol [Rjb::Proxy ~> A4Solution]
        # @return [Rjb::Proxy ~> SafeList<ExprVar>]
        def all_atoms(a4sol)
          a4sol.getAllAtoms
        end

        # Returns a hash of tuples grouped by field names.
        #
        # @param alloy_fields [Array(Rjb::Proxy ~> Sig$Field)]
        # @param a4sol [Rjb::Proxy ~> A4Solution]
        # @return [Hash(String, Array(Tuple))], where Tuple is Array(Atom)
        def field_tuples(alloy_fields, a4sol)
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
      end

    end
  end
end
