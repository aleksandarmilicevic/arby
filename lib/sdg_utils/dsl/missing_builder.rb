require 'alloy/ast/types'

require 'sdg_utils/dsl/base_builder'
require 'sdg_utils/proxy'

module SDGUtils
  module DSL

    class MissingBuilder < Proxy
      attr_reader :name, :args, :ret_type, :body, :super

      def initialize(name, &block)
        super(name)
        @name = name
        @args = {}
        @ret_type = notype
        @state = :init
        @body = block
        @super = nil
        if BaseBuilder.in_builder?
          @dsl_builder = BaseBuilder.get
          @dsl_builder.register_missing_builder(self)
        end
      end

      def consume()
        if @dsl_builder
          @dsl_builder.unregister_missing_builder(self)
        end
      end

      def in_init?()     @state == :init end
      def in_args?()     @state == :args end
      def in_ret_type?() @state == :ret_type end
      def past_init?()   in_args? || in_ret_type? end
      def past_args?()   in_ret_type? end
      def has_body?()    !!@body end

      def <(super_thing)
        @super = super_thing
        @state = :ret_type
        self
      end

      def [](*args)
        case @state
        when :init
          @args = to_args_hash(args)
          @state = :args
        when :args
          msg = "can only specify 1 arg for return type"
          ::Kernel.raise ::SDGUtils::DSL::SyntaxError, msg unless args.size == 1
          @ret_type = args[0]
          @state = :ret_type
        else
          ::Kernel.raise ::SDGUtils::DSL::SyntaxError, "only two calls to [] allowed"
        end
        self
      end

      # def respond_to?(sym)
      #   self.class.instance_methods.include? sym
      # end

      # def method_missing(sym, *args, &block)
      #   msg = "Tried to invoke `#{sym}' on a #{self.class} (`#{to_s}') object. "
      #   msg += "It's likely you mistakenly misspelled `#{@name}' in the first place"
      #   ::Kernel.raise ::NameError, msg
      # end

      def ==(other)
        if ::SDGUtils::DSL::MissingBuilder === other
          @name == other.name
        else
          @name == other
        end
      end

      def class()  ::SDGUtils::DSL::MissingBuilder end
      def hash()   @name.hash end
      def to_str() name.to_s end

      def to_s
        ans = name.to_s
        ans += "[#{args}]" if past_init?
        ans += "[#{ret_type}]" if past_args?
        ans += " <block>" if body
        ans
      end

      #--------------------------------------------------------
      # Returns the original missing symbol
      #--------------------------------------------------------
      def to_sym() @name end

      #--------------------------------------------------------
      # Converts self to +Alloy::Ast::UnaryType+ and then delegates
      # the +*+ operation to it.
      #
      # @see Alloy::Ast::AType
      # @see Alloy::Ast::UnaryType
      # @see Alloy::Ast::ProductType
      #--------------------------------------------------------
      def *(rhs)
        ::Alloy::Ast::UnaryType.new(self) * rhs
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
