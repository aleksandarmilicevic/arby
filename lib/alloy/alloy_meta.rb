require 'sdg_utils/meta_utils'
require 'sdg_utils/event/events'
require 'sdg_utils/caching/searchable_attr'

module Alloy
  extend self

  module Model

    module MMUtils
      include SDGUtils::Caching::SearchableAttr

      def self.included(base)
        base.extend SDGUtils::Caching::SearchableAttr::Static
      end

      def clear_restriction
        restrict_to nil
      end

      def restrict_to(mod)
        @restriction_mod = mod
      end

      protected

      def _restrict(src)
        return src unless @restriction_mod
        src.select {|e|
          e.name && e.name.start_with?(@restriction_mod.to_s + "::")}
      end
    end

    # ==================================================================
    # == Class +MetaModel+
    # ==================================================================
    class MetaModel
      include MMUtils
      include SDGUtils::Events::EventProvider

      def initialize
        reset
      end

      def reset
        @models = []
        @sigs = []
        @restriction_mod = nil
        @cache = {}
      end

      gen :model, :sig

      def open_model(mod)
        @opened_model =
          case mod
          when String, Symbol
            model!(mod.to_s)
          when Alloy::Ast::Model
            mod
          else
            raise ArgumentError, "#{mod}:#{mod.class} is neither String nor Model"
          end
      end

      def close_model(mod)
        msg = "#{mod} is not the currently opened model"
        raise ArgumentError, msg unless @opened_model == mod
        @opened_model = nil
      end

    end

  end
end
