require 'my_test_helper'
require 'alloy/ast/expr_builder'

module Alloy
  module Ast

    class ExprBuilderTest < Test::Unit::TestCase
      include SDGUtils::Testing::Assertions

      include Alloy::Ast::Ops

      def test_unknown
        assert_raise(ArgumentError) do
          ExprBuilder.apply(UNKNOWN, 1, 2)
        end

        assert_raise(ArgumentError) do
          ExprBuilder.apply(UNKNOWN)
        end
      end

      def test_equals
        ans = ExprBuilder.apply(EQUALS, 1, 2)
        assert Expr::BinaryExpr === ans
        assert_equal EQUALS, ans.op
        assert_equal 1, ans.lhs
      end

    end
  end
end
