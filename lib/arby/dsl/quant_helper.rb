require 'arby/ast/expr'
require 'arby/ast/decl'

module Arby
  module Dsl

    module QuantHelper
      include ExprHelper

      def all(decls, &body)    Arby::Ast::Expr::QuantExpr.all(_norm(decls), body) end
      def no(decls, &body)     Arby::Ast::Expr::QuantExpr.no(_norm(decls), body) end
      def one(decls, &body)    Arby::Ast::Expr::QuantExpr.one(_norm(decls), body) end
      def lone(decls, &body)   Arby::Ast::Expr::QuantExpr.lone(_norm(decls), body) end
      def exist(decls, &body)  Arby::Ast::Expr::QuantExpr.exist(_norm(decls), body) end
      def let(decls, &body)    Arby::Ast::Expr::QuantExpr.let(_norm(decls), body) end
      def select(decls, &body) Arby::Ast::Expr::QuantExpr.setcph(_norm(hash), body) end

      def no(expr)   (block_given?) ? no(expr, &Proc.new)    : _mult(:no, expr) end
      def one(expr)  (block_given?) ? one(expr, &Proc.new)   : _mult(:one, expr) end
      def lone(expr) (block_given?) ? lone(expr, &Proc.new)  : _mult(:lone, expr) end
      def some(expr) (block_given?) ? exist(expr, &Proc.new) : _mult(:some, expr) end

      private

      def _mult(meth, *args)
        ExprHelper.instance_method(meth).bind(self).call(*args)
      end

      def _norm(decl_hash)
        decls = []
        _traverse_fields_hash decl_hash, proc{ |arg_name, dom|
          # d = Arby::Ast::Decl.new :name => arg_name, :domain => dom
          d = Arby::Ast::Arg.new :name => arg_name, :type => dom
          decls << d
        }
        decls
      end

    end

  end
end
