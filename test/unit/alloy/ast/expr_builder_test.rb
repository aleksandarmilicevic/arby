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

      def test_product
        lhs = SigA.to_alloy_expr
        rhs = SigB.to_alloy_expr
        ans = ExprBuilder.apply(PRODUCT, lhs, rhs)
        assert Expr::BinaryExpr === ans
        assert_equal PRODUCT, ans.op
        assert_equal lhs, ans.lhs
        assert_equal rhs, ans.rhs
        puts "$$$$"
        puts ans
        puts "#%%%%%"
        assert_type [SigA, SigB], ans
      end

      def test_int_bin_ops
        ops = [LT, LTE, GT, GTE, REM, NOT_LT, NOT_LTE, NOT_GT, NOT_GTE, IPLUS, IMINUS, DIV, MUL, PLUSPLUS]
        ops.each do |op|
          lhs, rhs = 2, 3
          ans = ExprBuilder.apply(op, lhs, rhs)
          assert Expr::BinaryExpr === ans
          assert_equal op, ans.op
          assert_equal lhs, ans.lhs
          assert_equal rhs, ans.rhs
        end
      end

      def test_srting_bin_ops
        ops = [PLUS, MINUS]
        ops.each do |op|
          lhs, rhs = "Hello","o"
          ans = ExprBuilder.apply(op,lhs,rhs)
          assert Expr::BinaryExpr === ans
          assert_equal op, ans.op
          assert_equal lhs, ans.lhs
          assert_equal rhs, ans.rhs
        end
      end

      def test_equality_ops
        ops = [EQUALS, NOT_EQUALS]
        ops.each do |op|
          lhs, rhs = 2, 2
          ans = ExprBuilder.apply(op,lhs,rhs)
          assert Expr::BinaryExpr === ans
          assert_equal op, ans.op
          assert_equal lhs, ans.lhs
          assert_equal rhs, ans.rhs
        end
      end

      def test_unknown
        assert_raise(ArgumentError) do
          ExprBuilder.apply(UNKNOWN, 1, 2)
        end
      end
    end
  end
end
