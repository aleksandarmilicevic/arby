require 'alloy/dsl/abstract_helper'
require 'alloy/dsl/mult_helper'
require 'alloy/dsl/sig_builder'
require 'alloy/ast/model'

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
        meta.sig_created(ans)
        ans
      end

      def abstract_sig(name, fields={}, &block)
        sig(name, fields, &block).abstract
      end

      def __created(name)
        require 'alloy/alloy.rb'
        mod = Alloy.meta.find_model(name) || Alloy::Ast::Model.new(self, name)
        Alloy.meta.model_created(mod)
        define_singleton_method :meta, lambda{mod}
      end

      def __eval_body(&body)
        mod = meta()
        Alloy.meta.open_model(mod)
        begin
          mod.ruby_module.module_eval &body
        ensure
          Alloy.meta.close_model(mod)
        end
      end

    end

  end
end
