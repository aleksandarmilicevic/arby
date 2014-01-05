require 'arby/ast/expr'
require 'arby/ast/decl'

module Arby
  module Dsl

    module QuantHelper
      include FieldsHelper
      include ExprHelper

      def all(decl_hash, &block)
        decls = _to_decls(decl_hash)
        Arby::Ast::Expr::QuantExpr.all(decls, block)
      end

      def exist(decl_hash, &block)
        decls = _to_decls(decl_hash)
        Arby::Ast::Expr::QuantExpr.exist(decls, block)
      end

      def let(decl_hash, &block)
        decls = _to_decls(decl_hash)
        Arby::Ast::Expr::QuantExpr.let(decls, block)
      end

      def select(decl_hash, &block)
        decls = _to_decls(decl_hash)
        Arby::Ast::Expr::QuantExpr.comprehension(decls, block)
      end

      def some(expr, &block)
        if block
          exist(expr, &block)
        else
          _call_from_expr(:some, expr)
        end
      end

      def no(expr, &block)
        if block
          all(expr, &block).not
        else
          _call_from_expr(:no, expr)
        end
      end

      private

      def _call_from_expr(meth, *args)
        ExprHelper.instance_method(meth).bind(self).call(*args)
      end

      def _to_decls(decl_hash)
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
