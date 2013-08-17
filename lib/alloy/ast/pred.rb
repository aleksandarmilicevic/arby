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

      def initialize(hash)
        @parent   = hash[:parent]
        @name     = hash[:name].to_s.to_sym
        @args     = hash[:args]
        @ret_type = Alloy::Ast::AType.get(hash[:ret_type])
        @body     = hash[:body]
        #TODO: check types
        check_iden @name, "function name"
      end

      def arity() args.size end

      def to_opts
        instance_variables.reduce({}) do |acc,sym|
          acc.merge!({sym[1..-1].to_sym => instance_variable_get(sym)})
        end
      end
    end

    # ============================================================================
    # == Class +FunBuilder+
    #
    # Used to handle expressions like
    #   func_name[a: A, b: B][Int]
    # ============================================================================
    class FunBuilder < BasicObject
      attr_reader :name, :args, :ret_type

      def initialize(name)
        @name = name
        @args = {}
        @ret_type = notype
        @state = :init
      end

      def [](*args)
        case @state
        when :init
          @args = to_args_hash(args)
          @state = :args
        when :args
          msg = "can only specify 1 arg for fun return type"
          ::Kernel.raise ::Alloy::Ast::SyntaxError, msg unless args.size == 1
          @ret_type = args[0]
          @state = :ret_type
        else
          ::Kernel.raise ::Alloy::Ast::SyntaxError, "only two calls to [] allowed"
        end
        self
      end

      def method_missing(sym, *args, &block)
        ::Kernel.raise ::NameError, "undefined local variable or method `#{@name}'"
      end

      private

      def notype() ::Alloy::Ast::NoType.new end

      def to_args_hash(args)
        case
        when args.size == 1 && ::Hash === args[0]
          args[0]
        else
          # treat as a list of arg names
          args.reduce({}) do |acc, arg_name|
            acc.merge!({arg_name => notype})
          end
        end
      end
    end

  end
end
