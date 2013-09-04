require 'sdg_utils/proxy'

module SDGUtils
  module DSL

    class MissingConst < SDGUtils::Proxy
      def initialize(sym)
        super(sym)
        @sym = sym
      end

      #--------------------------------------------------------
      # Returns the original missing symbol
      #--------------------------------------------------------
      def to_sym() @sym end

      #--------------------------------------------------------
      # Overrides the +<+ operator so that, when in Alloy Dsl
      # context and the +rhs+ operand is of type +Class+, it
      # returns a +[self, rhs]+ tuple so that the context
      # can interpret it as sig extension.
      #
      # @see String#<
      #--------------------------------------------------------
      def <(rhs)
        super unless in_alloy_dsl?
        case rhs
        when Class, Symbol
          [self, rhs]
        else
          super
        end
      end

      #--------------------------------------------------------
      # Converts this class to +Alloy::Ast::UnaryType+ and
      # then delegates the +*+ operation to it.
      #
      # @see Alloy::Ast::AType
      # @see Alloy::Ast::UnaryType
      # @see Alloy::Ast::ProductType
      #--------------------------------------------------------
      def *(rhs)
        if in_alloy_dsl?
          Alloy::Ast::UnaryType.new(self) * rhs
        else
          super
        end
      end
    end

  end
end
