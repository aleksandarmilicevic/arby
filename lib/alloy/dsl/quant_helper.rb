require 'alloy/ast/expr'
require 'alloy/ast/decl'

module Alloy
  module Dsl

    module QuantHelper
      include FieldsHelper

      def all(decl_hash, &block)
        decls = _to_decls(decl_hash)
        Alloy::Ast::Expr::QuantExpr.all(decls, block)
      end

      def exist(decl_hash, &block)
        decls = _to_decls(decl_hash)
        Alloy::Ast::Expr::QuantExpr.exist(decls, block)
      end

      alias_method :some, :exist

      private

      def _to_decls(decl_hash)
        decls = []
        _traverse_fields_hash decl_hash, proc{ |arg_name, dom|
          # d = Alloy::Ast::Decl.new :name => arg_name, :domain => dom
          d = Alloy::Ast::Arg.new :name => arg_name, :type => dom
          decls << d
        }
        decls
      end

    end

  end
end
