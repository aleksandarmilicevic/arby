require 'sdg_utils/meta_utils'
require 'sdg_utils/event/events'

module Alloy
  extend self

  module Model

    module MMUtils
      def clear_restriction
        restrict_to nil
      end

      def restrict_to(mod)
        @restriction_mod = mod
      end

      protected

      def _cache(col, name, cache_var=@cache)
        cache_var[name] ||= _find_by_name(col, name)
      end

      def _restrict(src)
        return src unless @restriction_mod
        src.select {|e|
          e.name && e.name.start_with?(@restriction_mod.to_s + "::")}
      end

      def _find_by_name(col, name)
        col.find {|e| e.name == name}
      end

      def _search_by_name(col, name)
        return nil unless name
        col.find {|e| e.relative_name == name.relative_name}
      end
    end

    # ==================================================================
    # == Class +MetaModel+
    #
    # @attr records  [Hash] - maps record name to record class
    # @attr machines [Hash] - maps machine name to machine class
    # @attr events   [Hash] - maps event name to event class
    # ==================================================================
    class MetaModel
      include MMUtils
      include SDGUtils::Events::EventProvider

      private

      def initialize
        reset
      end

      public

      def sigs;  _sigs end
      def sig_created(sig_cls) @sigs << sig_cls end
      def sig_for_name(name);  _cache(_sigs, name) end
      def find_sig(name);      _search_by_name(sigs, name) end

      def reset
        #sigs.each { |s| SDGUtils::MetaUtils.undef_class(s) }
        @sigs = []
        @restriction_mod = nil
        @cache = {}
      end

      protected

      def _sigs; _restrict(@sigs) end

    end

  end
end
