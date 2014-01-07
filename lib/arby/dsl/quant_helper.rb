require 'arby/ast/expr'
require 'arby/ast/decl'

module Arby
  module Dsl

    module QuantHelper
      include ExprHelper

      def all(decl_hash, &block)
        decls = _to_decls(decl_hash)
        Arby::Ast::Expr::QuantExpr.all(decls, block)
      end

      def exist(decl_hash, &block) 
        Arby::Ast::Expr::QuantExpr.exist(_to_decls(decl_hash), block)
      end

      def let(decl_hash, &block)
        Arby::Ast::Expr::QuantExpr.let(_to_decls(decl_hash), block)
      end

      def select(decl_hash, &block)
        Arby::Ast::Expr::QuantExpr.comprehension(_to_decls(decl_hash), block)
      end

      def some(expr) (block_given?) ? exist(expr, &Proc.new)   : _mult(:some, expr) end
      def no(expr)   (block_given?) ? all(expr, &Proc.new).not : _mult(:no, expr) end

      private

      def _mult(meth, *args)
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
