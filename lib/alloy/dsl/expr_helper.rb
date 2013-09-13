require 'alloy/ast/expr'

module Alloy
  module Dsl

    module ExprHelper
      def no(expr) Alloy::Ast::Expr::UnaryExpr.no(expr) end
    end

  end
end
