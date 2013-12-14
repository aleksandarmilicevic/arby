require 'arby/ast/expr'

module Arby
  module Dsl

    module ExprHelper
      def no(expr) Arby::Ast::Expr::UnaryExpr.no(expr) end
    end

  end
end
