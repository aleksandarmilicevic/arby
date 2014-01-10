require 'arby/ast/expr'
require 'arby/ast/decl'

module Arby
  module Dsl

    module QuantHelper
      include ExprHelper

      def all(decls, &body)    _quant(:all, decls, body)   end
      def exist(decls, &body)  _quant(:exist, decls, body) end
      def let(decls, &body)    _quant(:let, decls, body)   end
      def select(decls, &body) _quant(:setcph, hash, body) end

      def no(expr, &body)   (body) ? _quant(:no, expr, body)    : _mult(:no, expr)   end
      def one(expr, &body)  (body) ? _quant(:one, expr, body)   : _mult(:one, expr)  end
      def lone(expr, &body) (body) ? _quant(:lone, expr, body)  : _mult(:lone, expr) end
      def some(expr, &body) (body) ? _quant(:exist, expr, body) : _mult(:some, expr) end

      private

      def _quant(kind, decls, body)
        Arby::Ast::Expr::QuantExpr.send kind, _norm(decls), body
      end

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
