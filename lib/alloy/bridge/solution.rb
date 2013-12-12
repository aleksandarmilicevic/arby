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
        Translator.translate_atoms(@a4sol)
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
        Translator.recreate_object_graph(@compiler._a4world, @a4sol)
      end

      # Translates this Alloy solution to an aRby instance.
      #
      # @see Translator.to_instance
      #
      # @return [Alloy::Ast::Instance]
      def instance()
        fail_if_unsat
        Translator.to_instance(@compiler._a4world, @a4sol)
      end

      private

      def fail_if_no_solution
        fail "no A4Solution given" unless @a4sol
      end

      def fail_if_unsat
        fail_if_no_solution
        fail "No instance found (the problem is unsatisfiable)" unless satisfiable?
      end

    end
  end
end
