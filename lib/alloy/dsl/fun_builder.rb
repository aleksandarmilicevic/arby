require 'alloy/ast/types'
require 'alloy/dsl/errors'

module Alloy
  module Dsl

    # ============================================================================
    # == Class +FunBuilder+
    #
    # Used to handle expressions like
    #   func_name[a: A, b: B][Int]
    # ============================================================================
    class FunBuilder < BasicObject
      attr_reader :name, :args, :ret_type, :body

      def initialize(name, &block)
        @name = name
        @args = {}
        @ret_type = notype
        @state = :init
        @body = block
      end

      def in_init?()     @state == :init end
      def in_args?()     @state == :args end
      def in_ret_type?() @state == :ret_type end
      def past_init?()   in_args? || in_ret_type? end
      def past_args?()   in_ret_type? end

      def [](*args)
        case @state
        when :init
          @args = to_args_hash(args)
          @state = :args
        when :args
          msg = "can only specify 1 arg for fun return type"
          ::Kernel.raise ::Alloy::Dsl::SyntaxError, msg unless args.size == 1
          @ret_type = args[0]
          @state = :ret_type
        else
          ::Kernel.raise ::Alloy::Dsl::SyntaxError, "only two calls to [] allowed"
        end
        self
      end

      def method_missing(sym, *args, &block)
        msg = "Tried to invoke `#{sym}' on a FunBuilder (`#{to_s}') object. "
        msg += "It's likely you mistakenly misspelled `#{@name}' in the first place"
        ::Kernel.raise ::NameError, msg
      end

      def ==(other)
        if ::Alloy::Dsl::FunBuilder === other
          @name == other.name
        else
          @name == other
        end
      end

      def class()  ::Alloy::Dsl::FunBuilder end
      def hash()   @name.hash end
      def to_str() name.to_s end

      def to_s
        ans = name.to_s
        ans += "[#{args}]" if past_init?
        ans += "[#{ret_type}]" if past_args?
        ans
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
