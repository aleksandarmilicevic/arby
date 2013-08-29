require 'alloy/dsl/mod_builder'

module Alloy
  module Dsl

    # ================================================================
    # == Module +Mult+
    #
    # Methods for constructing expressions.
    # ================================================================
    module MultHelper
      extend self
      def lone(*sig) ModBuilder.mult(:lone, *sig) end
      def one(*sig)  ModBuilder.mult(:one, *sig) end
      def set(*sig)  ModBuilder.mult(:set, *sig) end
      def seq(*sig)  ModBuilder.mult(:seq, *sig) end
    end

  end
end
