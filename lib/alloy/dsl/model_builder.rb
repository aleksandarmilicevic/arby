require 'alloy/dsl/model_api'
require 'sdg_utils/dsl/module_builder'

module Alloy
  module Dsl

    # ============================================================================
    # == Class +ModelBuilder+
    #
    # Used for creating alloy modules.
    #
    # NOTE: not thread safe!
    # ============================================================================
    class ModelBuilder < SDGUtils::DSL::ModuleBuilder

      #--------------------------------------------------------
      # Returns whether the evaluation is in the context
      # of the Alloy Dsl.
      #--------------------------------------------------------
      def self.in_dsl_context?
        curr = self.get and curr.in_module?
      end

      def initialize(options={})
        opts = {
          :mods_to_include => [ModelDslApi]
        }.merge!(options)
        super(opts)
      end

      #--------------------------------------------------------
      # Creates a modules named +name+ and then executes +&block+
      # using +module_eval+.  All Alloy sigs must be created inside an
      # "alloy model" block.  Inside of this module, all undefined
      # constants are automatically converted to symbols.
      # --------------------------------------------------------
      def model(model_sym, name, &block)
        raise RuntimeError, "Model nesting is not allowed" if in_module?
        @curr_model = model_sym
        build(name, &block)
      end

      def curr_model() @curr_model end
      def in_model() in_module? end
    end

  end
end
