require 'sdg_utils/errors'
require 'sdg_utils/dsl/syntax_error'

module Alloy
  module Dsl

    class SyntaxError < SDGUtils::Errors::ErrorWithCause
    end

  end
end

module SDGUtils
  module DSL
    class SyntaxError
      def class
        Alloy::Dsl::SyntaxError
      end
    end
  end
end
