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
      def lone(*sig, &blk) ModBuilder.mult(:lone, *sig, &blk) end
      def one(*sig, &blk)  ModBuilder.mult(:one, *sig, &blk) end
      def set(*sig, &blk)  ModBuilder.mult(:set, *sig, &blk) end
      def seq(*sig, &blk)  ModBuilder.mult(:seq, *sig, &blk) end
    end

  end
end
