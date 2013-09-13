require 'alloy/dsl/helpers'
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
      include QuantHelper
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
        SigBuilder.new({:return => :builder}).sig(name, fields, &block)
        # ans = sb.sig(name, fields, &block)
        # sigs = (Array === ans) ? ans : [ans]
        # sigs.each do |sig|
        #   sig.abstract if @abstract_alloy_block
        # end
        # sigs
      end

      # def abstract_sig(name, fields={}, &block)
      #   sig(name, fields, &block).abstract
      # end

      def __created(scope_module)
        require 'alloy/alloy.rb'
        mod = Alloy.meta.find_model(name) || __create_model(scope_module)
        Alloy.meta.add_model(mod)
        __define_meta(mod)
      end

      def __eval_body(&body)
        mod = meta()
        Alloy.meta.open_model(mod)
        begin
          mod.ruby_module.module_eval(&body)
        ensure
          Alloy.meta.close_model(mod)
        end
      end

      def __create_model(scope_module)
        Alloy::Ast::Model.new(scope_module, self)
      end

      def __define_meta(alloy_model)
        define_singleton_method :meta, lambda{alloy_model}
      end

    end

  end
end
