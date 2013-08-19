require 'alloy/dsl/helpers'
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
      include FunHelper
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
        sigs = (Array === ans) ? ans : [ans]
        sigs.each do |sig|
          sig.abstract if @abstract_alloy_block
          meta.add_sig(sig)
        end
        sigs
      end

      def abstract_sig(name, fields={}, &block)
        sig(name, fields, &block).abstract
      end

      def __created(name)
        require 'alloy/alloy.rb'
        mod = Alloy.meta.find_model(name) || Alloy::Ast::Model.new(self, name)
        Alloy.meta.add_model(mod)
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
