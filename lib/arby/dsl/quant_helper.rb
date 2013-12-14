require 'arby/ast/expr'
require 'arby/ast/decl'

module Arby
  module Dsl

    module QuantHelper
      include FieldsHelper

      def all(decl_hash, &block)
        decls = _to_decls(decl_hash)
        Arby::Ast::Expr::QuantExpr.all(decls, block)
      end

      def exist(decl_hash, &block)
        decls = _to_decls(decl_hash)
        Arby::Ast::Expr::QuantExpr.exist(decls, block)
      end

      alias_method :some, :exist

      private

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
