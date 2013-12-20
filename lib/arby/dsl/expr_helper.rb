require 'arby/ast/expr'

module Arby
  module Dsl

    module ExprHelper
      def no(expr) Arby::Ast::Expr::UnaryExpr.no(expr) end
      def some(expr) Arby::Ast::Expr::UnaryExpr.some(expr) end
    end

  end
end
