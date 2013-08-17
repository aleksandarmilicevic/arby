require 'alloy/dsl/model_builder'

module Alloy

  # ================================================================
  # == Module +Dsl+
  #
  # Included in all user defined (via the +AlloyDsl::Dsl#alloy_model+
  # method) Alloy models.
  # ================================================================
  module Dsl
    extend self

    module StaticHelpers
      include MultHelper
      extend self
    end

    #TODO: doesn't work for ActiveRecord::Relation
    module InstanceHelpers
      require 'alloy/relations/relation_ext.rb'
      def no(col)   col.as_rel.no? end
      def some(col) col.as_rel.some? end
      def one(col)  col.as_rel.one? end
      def lone(col) col.as_rel.lone? end
    end

    # ----------------------------------------------------------------
    # Creates a modules named +name+ and then executes +&block+ using
    # +module_eval+.  All Alloy sigs must be created inside an "alloy
    # model" block.  Inside of this module, all undefined constants
    # are automatically converted to symbols.
    # ----------------------------------------------------------------
    def alloy_model(name="", &block)
      ModelBuilder.new.model(:alloy, name, &block)
    end

    # ----------------------------------------------------------------
    # Different aliases for the +alloy_model+ method.
    # ----------------------------------------------------------------
    alias_method :alloy_module, :alloy_model

  end

end

require 'alloy/dsl/ext.rb'
