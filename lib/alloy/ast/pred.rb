require 'alloy/ast/types'

module Alloy
  module Ast

    class Fun
      attr_reader :parent, :name, :args, :ret_type, :body

      def initialize(hash)
        @parent   = hash[:parent]
        @name     = hash[:name].to_s.to_sym
        @args     = hash[:args]
        @ret_type = Alloy::Ast::AType.get(hash[:ret_type])
        @body     = hash[:body]
        #TODO: check types
      end

      def to_opts
        instance_variables.reduce({}) do |acc,sym|
          acc.merge!({sym[1..-1].to_sym => instance_variable_get(sym)})
        end
      end
    end

  end
end
