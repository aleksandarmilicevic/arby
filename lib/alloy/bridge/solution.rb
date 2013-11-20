require 'alloy/bridge/imports'
module Alloy
  module Bridge
    class Solution

      def initialize(a4sol, compiler=nil)
        @a4sol = a4sol
        @compiler = compiler
      end

      def all_atoms
        fail_if_no_solution
        self.class.all_atoms(@a4sol)
      end

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

        Atom = Struct.new(:name, :a4type)

        # Takes a proxy to an Alloy solution and extract a list of all
        # atoms from it.
        # 
        # @param a4sol [Rjb::Proxy ~> A4Solution]
        # @return [Rjb::Proxy ~> SafeList<ExprVar>]
        def all_atoms(a4sol)
          return a4sol.getAllAtoms        
        end

        def field_tuples(alloy_fields, a4sol)
          map = alloy_fields.map do |field|
            key = field.label
            a4_tuple_set = a4sol.eval(field)
            a4_iterator = a4_tuple_set.iterator
            tuples = []
            while a4_iterator.hasNext
              t = a4_iterator.next
              tuples << (0...t.arity).map {|j| Atom.new(t.atom(j), t.sig(j)) }
            end
            [key, tuples]
          end
          Hash[map]
        end

        
      end

    end
  end
end
