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

      class << self
        def fun(hash)
          Fun.new(:fun, hash)
        end

        def pred(hash)
          hash = ensure_bool_ret(hash.clone)
          Fun.new(:pred, hash)
        end

        def fact(hash)
          hash = ensure_bool_ret(hash.clone)
          hash = ensure_no_args(hash)
          Fun.new :fact, hash
        end

        def assertion(hash)
          hash = ensure_bool_ret(hash.clone)
          hash = ensure_no_args(hash)
          Fun.new :assertion, hash
        end

        private

        def ensure_bool_ret(hash)
          rt = hash[:ret_type]
          unless rt.nil? || Alloy::Ast::NoType === rt
            at = Alloy::Ast::AType.get(rt)
            msg = "expected bool return type, got #{at}"
            raise ArgumentError, msg unless (at.isBool? rescue false)
          end
          hash[:ret_type] = :Bool
          hash
        end

        def ensure_no_args(hash)
          args = hash[:args]
          msg = "expected no arguments"
          raise ArgumentError, msg unless args.nil? || args.empty?
          hash[:args] = []
          hash
        end
      end

      private

      def initialize(kind, hash)
        @kind     = kind
        @parent   = hash[:parent]
        @name     = check_iden hash[:name].to_s.to_sym, "function name"
        @args     = hash[:args] || []
        @ret_type = Alloy::Ast::AType.get(hash[:ret_type])
        @body     = hash[:body] || proc{}
      end

      public

      def fun?()       @kind == :fun  end
      def pred?()      @kind == :pred  end
      def fact?()      @kind == :fact  end
      def assertion?() @kind == :assertion  end

      def arity()      args.size end
      def arg_types()  args.map(&:type) end
      def full_type()  (arg_types + [ret_type]).reduce(nil, &ProductType.cstr_proc) end

      def to_opts
        instance_variables.reduce({}) do |acc,sym|
          acc.merge!({sym[1..-1].to_sym => instance_variable_get(sym)})
        end
      end

      def to_s
        kind = pred?() ? "pred" : "fun"
        args_str = args.map{|a| "#{a.name}: #{a.type}"}.join(", ")
        "#{kind} #{name}[#{args_str}]: #{ret_type}"
      end
    end

  end
end
