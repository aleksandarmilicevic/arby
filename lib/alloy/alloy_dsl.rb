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
