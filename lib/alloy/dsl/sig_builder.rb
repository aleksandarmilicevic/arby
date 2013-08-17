require 'sdg_utils/dsl/class_builder'

module Alloy
  module Dsl

    # ============================================================================
    # == Class +SigBuilder+
    #
    # Used to create sig classes.
    # ============================================================================
    class SigBuilder < SDGUtils::DSL::ClassBuilder
      def initialize(options={})
        opts = {
          :superclass => Alloy::Ast::Sig
        }
        super(opts.merge!(options))
      end

      def self.sig(*args, &block)
        new.sig(*args, &block)
      end

      # --------------------------------------------------------------
      # Creates a new class, subclass of either +Alloy::Ast::Sig+ or a
      # user supplied super class, creates a constant with a given
      # +name+ in the callers namespace and assigns the created class
      # to it.
      # --------------------------------------------------------------
      def sig(name, fields={}, &block)
        build(name, fields, &block)
      end
    end


  end
end
