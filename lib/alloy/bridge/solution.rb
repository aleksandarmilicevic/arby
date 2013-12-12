require 'alloy/bridge/imports'
require 'alloy/bridge/translator'

module Alloy
  module Bridge
    class Solution

      def initialize(a4sol, compiler=nil)
        @a4sol = a4sol
        @compiler = compiler
      end

      def _a4sol
        @a4sol
      end

      def satisfiable?
        fail_if_no_solution
        @a4sol.satisfiable
      end

      def next()
        Solution.new(@a4sol.next(), @compiler)
      end

      # @see Solution.translate_atoms
      def translate_atoms
        fail_if_unsat
        self.class.translate_atoms(@a4sol)
      end

      # Translates the underlying solution from Alloy to aRby:
      #
      #   - the Alloy atoms are converted to instances of
      #     corresponding aRby sig classes (aRby atoms)
      #
      #   - the fields values of the aRby atoms are set to match the
      #     values of the Alloy field relations in this solution.
      #
      # @see Solution.translate_to_arby
      #
      # @return [Hash(String, Sig)] - a map of atom labels to aRby atoms
      def translate_to_arby()
        fail_if_unsat
        self.class.translate_to_arby(@compiler._a4world, @a4sol)
      end

      # Returns tuples grouped by field names.
      #
      # @see Solution.field_tuples
      #
      # @return [Hash(String, Array(Tuple))], where Tuple is Array(Atom)
      def field_tuples()
        fail_if_unsat
        self.class.field_tuples(@compiler._a4world, @a4sol)
      end

      private

      def fail_if_no_solution
        fail "no A4Solution given" unless @a4sol
      end

      def fail_if_unsat
        fail_if_no_solution
        fail "No instance found (the problem is unsatisfiable)" unless satisfiable?
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

        # Takes a proxy to an Alloy solution, extract a list of all
        # atoms from it and converts them to aRby atoms (instance of
        # corresponding aRby sig classes).
        #
        # @see Translator.translate_atoms
        #
        # @param a4sol [Rjb::Proxy ~> A4Solution]
        # @return [Array(Sig)]
        def translate_atoms(a4sol)
          Translator.translate_atoms(a4sol.getAllAtoms)
        end

        # @see Translator.recreate_object_graph
        #
        # @param a4world [Rjb::Proxy ~> CompModule]
        # @param a4sol [Rjb::Proxy ~> A4Solution]
        # @return [Hash(String, Sig)]               - a map of atom labels to atoms
        def translate_to_arby(a4world, a4sol)
          field_map = field_tuples(a4world, a4sol)
          atoms = translate_atoms(a4sol)
          Translator.recreate_object_graph(field_map, atoms)
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

      end

    end
  end
end
