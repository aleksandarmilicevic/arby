require 'arby/ast/tuple_set'
require 'arby/ast/type_checker'

module Arby
  module Ast

    # Rel: [Class(Arby::Ast::Sig), Arby::Ast::Field]
    #
    # @attr sig_lowers, sig_uppers [Hash(Rel, Arby::Ast::TupleSet)]
    # @attr fld_lowers, fld_uppers [Hash(Rel, Arby::Ast::TupleSet)]
    class Bounds

      def initialize
        @lowers, @uppers = {}
      end

      def bound(what, lower, upper)
        TypeChecker.check_arity(what, lower)
        TypeChecker.check_arity(what, upper)
        @lowers[what] = lower.dup
        @uppers[what] = upper.dup
      end

      def bound_exactly(what, tuple_set)
        bound(what, tuple_set, tuple_set)
      end

    end

  end
end
