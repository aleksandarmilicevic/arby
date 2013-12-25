require 'arby/ast/instance'
require 'arby/bridge/imports'
require 'arby/bridge/helpers'
require 'arby/bridge/translator'
require 'sdg_utils/proxy'

module Arby
  module Bridge

    # ------------------------------------------------------------------
    # Simple wrapper for an Alloy type.
    #
    # @attr a4type [Rjb::Proxy ~> edu.mit.csail.sdg.alloy4compiler.ast.Type]
    # @attr prim_sigs [Array(Rjb::Proxy ~> edu.mit.csail.sdg.alloy4compiler.ast.PrimSig)]
    # ------------------------------------------------------------------
    class Type
      include Helpers

      # @param a4type [ Rjb::Proxy ~> edu.mit.csail.sdg.alloy4compiler.ast.Type,
      #                 Array(Rjb::Proxy ~> edu.mit.csail.sdg.alloy4compiler.ast.PrimSig) ]
      def initialize(a4type)
        if Array === a4type
          @prim_sigs = a4type
        else
          @a4type = a4type
          union_types = a4type.fold
          fail "Union types not supported: #{a4type.toString}" unless union_types.size == 1
          @prim_sigs = java_to_ruby_array(union_types.get(0))
        end
        @signature = @prim_sigs.map(&:toString).join(" -> ")
      end

      def prim_sigs() @prim_sigs end
      def signature() @signature end
      def arity()     @prim_sigs.size end
      def to_s()      @signature end
    end

    # ------------------------------------------------------------------
    # Simple wrapper for an Alloy atom.
    #
    # @attr a4atom [Rjb::Proxy ~> edu.mit.csail.sdg.alloy4compiler.ast.ExprVar]
    # @attr label [String]
    # @attr type [Arby::Bridge::Type]
    # ------------------------------------------------------------------
    class Atom
      attr_reader :a4atom, :label, :type

      # Takes either an a4atom, or name/a4type pair.
      #
      # @param a4atom [Rjb::Proxy ~> edu.mit.csail.sdg.alloy4compiler.ast.ExprVar]
      # @param name [String]
      # @param a4type [Rjb::Proxy ~> edu.mit.csail.sdg.alloy4compiler.ast.Type]
      def initialize(a4atom, label=nil, type=nil)
        @a4atom = a4atom
        @label = a4atom ? a4atom.toString : label
        @type = Type.new(a4atom ? a4atom.type : type)
      end

      def to_s() "#{label}: #{type}" end
    end

    # ------------------------------------------------------------------
    # Simple wrapper for an Alloy TupleSet.
    #
    # @attr type [Arby::Bridge::Type]
    # @tuples [Array(Array(Arby::Bridge::Atom))]
    # ------------------------------------------------------------------
    class TupleSet < SDGUtils::Proxy
      attr_reader :type, :tuples

      def initialize(type, tuples)
        @type, @tuples = type, tuples
        super(@tuples)
      end
    end

    module SolutionConv
      include Helpers
      extend self

      # Returns an object of type +Arby::Ast::Instance+ with type
      # parameters +Atom+ and +TupleSet+ corrsponding to
      # +Arby::Bridge::Atom+ and +Arby::Bridge::TupleSet+.
      #
      # @param a4world [Rjb::Proxy ~> CompModule]
      # @param a4sol [Rjb::Proxy ~> A4Solution]
      # @return [Arby::Ast::Instance]
      def to_instance(a4world, a4sol)
        atoms = []
        fld_map = {}
        skolem_map = {}

        if a4sol.satisfiable
          atoms = wrap_atoms(a4sol)

          fld_map = Compiler.all_fields(a4world).map do |field|
            [field.label, eval_expr(a4sol, field)]
          end
          fld_map = Hash[fld_map]

          skolem_map = jmap(a4sol.getAllSkolems) do |expr|
            [expr.toString, eval_expr(a4sol, expr)]
          end
          skolem_map = Hash[skolem_map]
        end

        Arby::Ast::Instance.new atoms, fld_map, skolem_map, false
      end

      # Takes an Rjb Proxy object pointing to an A4Solution, gets all
      # atoms from it, and wraps them in +Arby::Bridge::Atom+.
      #
      # @param a4atoms [Rjb::Proxy -> A4Solution]
      # @return [Array(Arby::Bridge::Atom)]
      def wrap_atoms(a4sol)
        a4atoms = a4sol.getAllAtoms
        len = a4atoms.size
        (0...len).map{ |idx| Atom.new(a4atoms.get(idx)) }
      end

      # Returns a hash of tuples grouped by field names.
      #
      # @param a4sol [Rjb::Proxy ~> A4Solution]
      # @param a4sol [Rjb::Proxy ~> Expr]
      # @return [Arby::Bridge::TupleSet]
      def eval_expr(a4sol, a4expr)
        expr_type = Type.new(a4expr.type)
        expr_tuples = translate_tuple_set(a4sol.eval(a4expr))
        TupleSet.new(expr_type, expr_tuples)
      end

      # Traverses a given Alloy tupleset, wraps all atom in it, and
      # returns an array of arrays of atoms.
      #
      # @param a4tuple_set [Rjb::Proxy ~> A4TupleSet]
      # @return [Array(Array(Atom))]
      def translate_tuple_set(a4tuple_set)
        jmap_iter(a4tuple_set) do |t|
          (0...t.arity).map{|col| Atom.new(nil, t.atom(col), [t.sig(col)]) }
        end
      end

    end

    class Solution
      def initialize(a4sol, compiler=nil, solving_time=nil)
        @a4sol = a4sol
        @compiler = compiler
        @instance = nil
        @solving_time = solving_time
      end

      def _a4sol()   @a4sol end
      def compiler() @compiler end
      def instance() @instance ||= SolutionConv.to_instance(@compiler._a4world, @a4sol) end
      def next()     Solution.new(@a4sol.next(), @compiler) end

      def satisfiable?
        fail_if_no_solution
        @a4sol.satisfiable
      end

      def solving_time() @solving_time end

      # Translates the underlying solution from Alloy to aRby:
      #
      #   - the Alloy atoms are converted to instances of
      #     corresponding aRby sig classes (aRby atoms)
      #
      #   - the fields values of the aRby atoms are set to match the
      #     values of the Alloy field relations in this solution.
      #
      # @see SolutionConv.arby_instance
      #
      # @return [Hash(String, Sig)] - a map of atom labels to aRby atoms
      def arby_instance()
        return Arby::Ast::Instance.new unless satisfiable?
        @arby_instance ||= Translator.to_arby_instance(instance())
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
