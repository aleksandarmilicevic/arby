require 'alloy/dsl/sig_builder'
require 'alloy/dsl/abstract_helper'
require 'alloy/dsl/mult_helper'
require 'sdg_utils/dsl/module_builder'

module Alloy
  module Dsl

    # ============================================================================
    # == Class +Model+
    #
    # Module to be included in each +alloy_model+.
    # ============================================================================
    module ModelDslApi
      include MultHelper
      include AbstractHelper
      extend self

      protected

      # --------------------------------------------------------------
      # Creates a new class, subclass of either Alloy::Ast::Sig or a
      # user supplied super class, creates a constant with a given
      # +name+ in the callers namespace and assigns the created class
      # to it.
      # --------------------------------------------------------------
      def sig(name, fields={}, &block)
        ans = SigBuilder.sig(name, fields, &block)
        ans.abstract if @abstract_alloy_block
        ans
      end

      def abstract_sig(name, fields={}, &block)
        sig(name, fields, &block).abstract
      end
    end

    # ============================================================================
    # == Class +ModelBuilder+
    #
    # Used for creating alloy modules.
    #
    # NOTE: not thread safe!
    # ============================================================================
    class ModelBuilder < SDGUtils::DSL::ModuleBuilder
      def self.get() SDGUtils::DSL::ModuleBuilder.get end

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

    # # ============================================================================
    # # == Class +ModelBuilder+
    # #
    # # Used for creating alloy modules.
    # #
    # # NOTE: not thread safe!
    # # ============================================================================
    # class ModelBuilder < SDGUtils::DSL::ModuleBuilder
    #   def self.get() SDGUtils::DSL::ModuleBuilder.get end

    #   #--------------------------------------------------------
    #   # Returns whether the evaluation is in the context
    #   # of the Alloy Dsl.
    #   #--------------------------------------------------------
    #   def self.in_dsl_context?
    #     curr = self.get and curr.in_module?
    #   end

    #   def initialize(options={})
    #     opts = {
    #       :mods_to_include => [ModelDslApi]
    #     }.merge!(options)
    #     super(opts)
    #   end

    #   #--------------------------------------------------------
    #   # Creates a modules named +name+ and then executes +&block+
    #   # using +module_eval+.  All Alloy sigs must be created inside an
    #   # "alloy model" block.  Inside of this module, all undefined
    #   # constants are automatically converted to symbols.
    #   # --------------------------------------------------------
    #   def model(model_sym, name, &block)
    #     raise RuntimeError, "Model nesting is not allowed" if in_module?
    #     @curr_model = model_sym
    #     build(name, &block)
    #   end

    #   def curr_model() @curr_model end
    #   def in_model() in_module? end
    # end

  end
end
