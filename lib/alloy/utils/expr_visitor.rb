require 'alloy/ast/expr'

module Alloy
  module Utils

    class ExprVisitor

      def expr_to_als(expr)
        expr.class.ancestors.select{|cls|
          cls < Alloy::Ast::Expr::MExpr
        }.each do |cls|
          kind = cls.relative_name.downcase
          meth = "#{kind}_to_als".to_sym
          if self.respond_to? meth
            return self.send meth, expr
          end
        end
        @out.p expr.to_s
      end


    end

  end
end
