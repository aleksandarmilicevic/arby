require 'alloy/ast/expr'

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

      private

      def _to_decls(decl_hash)
        decls = []
        _traverse_fields_hash decl_hash, proc{ |arg_name, type|
          arg = Alloy::Ast::Arg.new :name => arg_name, :type => type
          decls << arg
          # decls << [key, value]
        }
        decls
      end

    end

  end
end
