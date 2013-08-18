require 'alloy/dsl/abstract_helper'
require 'alloy/dsl/mult_helper'
require 'alloy/dsl/sig_builder'

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

  end
end
