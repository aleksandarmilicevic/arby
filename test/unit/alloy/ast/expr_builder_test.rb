require 'my_test_helper'
require 'alloy/ast/expr_builder'
require 'alloy/alloy_dsl'

include Alloy::Dsl

alloy :A_A_EBT do
  sig SigA
  sig SigB
end


module Alloy
  module Ast

    class ExprBuilderTest < Test::Unit::TestCase
      include SDGUtils::Testing::Assertions
      include SDGUtils::Testing::SmartSetup

      include Alloy::Ast::Ops
      include A_A_EBT

      def setup_class
        Alloy.reset
        Alloy.meta.restrict_to(A_A_EBT)
        Alloy.initializer.resolve_fields
        Alloy.initializer.init_inv_fields

        # Alloy.set_symbolic_mode
      end

      def assert_type(type_array, expr)
        assert expr.respond_to?(:__type), "Expr `#{expr}' doesn't respond to __type"
        t = expr.__type
        assert t, "Expr `#{expr}' type is nil"
        assert_equal type_array.size, t.arity,
                     "Expected arity #{type_array.size}, actual #{t.arity}"
        assert_seq_equal type_array.map(&Alloy::Ast::AType.method(:get)), t.columns
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

      def test_in
        ans = ExprBuilder.apply(IN,0,[1,2,3])
        assert Expr::BinaryExpr === ans
        assert_equal IN, ans.op
      end

      def test_notIn
        ans = ExprBuilder.apply(NOT_IN,0,[1,2,3])
        assert Expr::BinaryExpr === ans
        assert_equal NOT_IN, ans.op

      end
      ## not sure what to put in lhs rhs
      def test_select
        ans = ExprBuilder.apply(SELECT,0,1)
        assert Expr::BinaryExpr === ans
        assert_equal SELECT, ans.op
      end

      def test_not
        ans = ExprBuilder.apply(NOT,1)
        assert Expr::UnaryExpr === ans
        assert_equal NOT, ans.op
      end


      def test_no
        ans = ExprBuilder.apply(NO,1)
        assert Expr::UnaryExpr === ans
        assert_equal NO, ans.op
      end

      def test_some
        ans = ExprBuilder.apply(SOME,1)
        assert Expr::UnaryExpr === ans
        assert_equal SOME, ans.op
      end


      def test_lone
        ans = ExprBuilder.apply(LONE,1)
        assert Expr::UnaryExpr === ans
        assert_equal LONE, ans.op
      end

      def test_one
        ans = ExprBuilder.apply(ONE,1)
        assert Expr::UnaryExpr === ans
        assert_equal ONE, ans.op
      end

      def test_product
        lhs = SigA.to_alloy_expr
        rhs = SigB.to_alloy_expr
        ans = ExprBuilder.apply(PRODUCT, lhs, rhs)
        assert Expr::BinaryExpr === ans
        assert_equal PRODUCT, ans.op
        assert_equal lhs, ans.lhs
        assert_equal rhs, ans.rhs
        assert_type [SigA, SigB], ans
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
