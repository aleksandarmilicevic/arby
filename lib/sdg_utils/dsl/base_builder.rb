require 'sdg_utils/track_nesting'

module SDGUtils
  module DSL

    #=========================================================================
    # == Class ClassBuilder
    #
    #=========================================================================
    class BaseBuilder
      extend SDGUtils::TrackNesting

      def self.top()             top_ctx end
      def self.get()             SDGUtils::DSL::BaseBuilder.find(self) end
      def self.find(builder_cls) find_ctx{|e| builder_cls === e} end
    end

  end
end
