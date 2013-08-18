require 'alloy/alloy_ast_errors'
require 'alloy/ast/types'
require 'alloy/ast/utils'

module Alloy
  module Ast

    # ============================================================================
    # == Class +Fun+
    #
    # Represents function definitions
    #
    # @attr :parent   [ASig]
    # @attr :name     [Symbol]
    # @attr :args     [Array(Arg)]
    # @attr :ret_type [AType]
    # @attr :body     [Proc]
    # ============================================================================
    class Fun
      include Checks

      attr_reader :parent, :name, :args, :ret_type, :body

      def self.fun(hash)
        self.new(hash)
      end

      def self.pred(hash)
        hash[:ret_type] ||= :Bool
        pred = self.new(hash)
        rt = pred.ret_type
        case
        when NoType === rt
          pred.instance_variable_set "@ret_type", Alloy::Ast::AType.get(:Bool)
        when (rt.isBool? rescue false)
          # ok
        else
          raise ArgumentError, "non-bool return type (#{rt}) specified for a pred"
        end
        pred.instance_variable_set "@is_pred", true
        pred
      end

      def initialize(hash)
        @parent   = hash[:parent]
        @name     = check_iden hash[:name].to_s.to_sym, "function name"
        @args     = hash[:args]
        @ret_type = Alloy::Ast::AType.get(hash[:ret_type])
        @body     = hash[:body]
      end

      def pred?()     @is_pred  end
      def arity()     args.size end
      def arg_types() args.map(&:type) end
      def full_type() (arg_types + [ret_type]).reduce(nil, &ProductType.cstr_proc) end

      def to_opts
        instance_variables.reduce({}) do |acc,sym|
          acc.merge!({sym[1..-1].to_sym => instance_variable_get(sym)})
        end
      end

      def to_s
        kind = pred?() ? "pred" : "fun"
        args_str = args.map{|a| "#{a.name}: #{a.type}"}.join(", ")
        "#{kind} [#{args_str}]: #{ret_type}"
      end
    end

  end
end
