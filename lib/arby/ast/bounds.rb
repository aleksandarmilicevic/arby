require 'arby/ast/field'
require 'arby/ast/sig'
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
        @lowers = {}
        @uppers = {}
      end

      def bound(what, lower, upper)
        TypeChecker.check_arity(what, lower)
        TypeChecker.check_arity(what, upper)
        check_field_or_sig(what)
        @lowers[what] = lower.dup
        @uppers[what] = upper.dup
        self
      end

      def bound_exactly(what, tuple_set)
        bound(what, tuple_set, tuple_set)
      end

      def add_lower(what, tuple_set)
        add_bound(@lowers, what, tuple_set)
        add_bound(@uppers, what, tuple_set)
      end

      def add_upper(what, tuple_set)
        add_bound(@uppers, what, tuple_set)
      end

      def get_lower(what) @lowers[what] end #dup ???
      def get_upper(what) @uppers[what] end #dup ???

      private

      def add_bound(where, what, tuple_set)
        check_field_or_sig(what)
        bnd = get_or_new(where, what)
        bnd.union!(tuple_set)
        self
      end

      def get_or_new(col, what)
        col[what] ||= TupleSet.wrap([], what)
      end

      def check_field_or_sig(what)
        unless what.is_a?(Field) || TypeChecker.check_sig_class(what)
          raise TypeError, "only Field instances or Sig class can be bound; got #{what}"
        end
      end
    end

  end
end
