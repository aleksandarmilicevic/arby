require 'alloy/bridge/imports'
module Alloy
  module Bridge
    class Solution

      def initialize(a4sol)
        @a4sol = a4sol
      end

      def all_atoms
        fail_if_no_solution
        self.class.all_atoms(@a4sol)
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

        # Takes a proxy to an Alloy solution and extract a list of all
        # atoms from it.
        # 
        # @param a4sol [Rjb::Proxy ~> A4Solution]
        # @return [Rjb::Proxy ~> SafeList<ExprVar>]
        def all_atoms(a4sol)
          return a4sol.getAllAtoms        
        end
      end

    end
  end
end
