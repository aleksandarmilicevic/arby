require 'alloy/ast/op'
require 'alloy/ast/expr'

module Alloy
  module Ast

    #TODO: move the "__type" method to MExpr

    module ExprBuilder
      extend self

      # Keep track of result type
      #
      # @param op [Alloy::Ast::Op] --- operator
      # @param args [Array(Expr)] --- operands
      def apply(op, *args)
        case op
        when Ops::UNKNOWN
          raise ArgumentError, "Cannot apply the unknown operator"
      
        when Ops::EQUALS, Ops::NOT_EQUALS, Ops::LT, Ops::LTE, Ops::GT, Ops::GTE, Ops::REM
          # TODO: check that args.length == 2
          ans = Expr::BinaryExpr.new(op, *args)
          #result_type = nil #TODO ...
          #Expr.add_methods_for_type(ans, result_type)
        end
      end
    end

  end
end
