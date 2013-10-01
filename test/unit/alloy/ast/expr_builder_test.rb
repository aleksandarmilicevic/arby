require 'my_test_helper'
require 'alloy/ast/expr_builder'

module Alloy
  module Ast

    class ExprBuilderTest < Test::Unit::TestCase
      include SDGUtils::Testing::Assertions

      include Alloy::Ast::Ops

      def setup
        # Alloy.set_symbolic_mode
      end

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

      def test_notEquals
        ans = ExprBuilder.apply(NOT_EQUALS,0,1)
        assert Expr::BinaryExpr === ans
        assert_equal NOT_EQUALS, ans.op
        assert_equal 1, ans.rhs
        assert_equal 0, ans.lhs
      end

      def test_lessThan
        ans = ExprBuilder.apply(LT,0,1)
        assert Expr::BinaryExpr === ans
        assert_equal LT, ans.op
        assert_equal 1, ans.rhs
        assert_equal 0, ans.lhs
      end

      def test_lessThanEqual
        ans = ExprBuilder.apply(LTE,2,2)
        assert Expr::BinaryExpr === ans
        assert_equal LTE, ans.op
        assert_equal ans.rhs, ans.lhs
      end

      def test_greaterThan
        ans = ExprBuilder.apply(GT,0,1)
        assert Expr::BinaryExpr === ans
        assert_equal GT, ans.op
        assert_equal 1, ans.rhs
      end

      def test_greaterThanEquals
        ans = ExprBuilder.apply(GTE,6,5)
        assert Expr::BinaryExpr === ans
        assert_equal GTE, ans.op
        assert_equal 5, ans.rhs
      end
      
      def test_rem
        ans = ExprBuilder.apply(REM,10,5)
        assert Expr::BinaryExpr === ans
        assert_equal REM, ans.op
        puts "#$$$$$$"
        puts ans
        puts "#$$$$$"
      end

      def test_int_bin_ops
        ops = [LT, LTE, GT, GTE, REM]
        ops.each do |op|
          lhs, rhs = 2, 3
          ans = ExprBuilder.apply(op, lhs, rhs)
          assert Expr::BinaryExpr === ans
          assert_equal op, ans.op
          assert_equal lhs, ans.lhs
          assert_equal rhs, ans.rhs
        end
      end

    end
  end
end
