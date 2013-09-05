require 'alloy/ast/sig'
require 'sdg_utils/dsl/class_builder'

module Alloy
  module Dsl

    # class NameSuperclassPair
    #   attr_reader :name, :supercls
    #   def initialize(name, supercls)
    #     @name, @supercs = name, supercls
    #   end
    # end

    # ============================================================================
    # == Class +SigBuilder+
    #
    # Used to create sig classes.
    # ============================================================================
    class SigBuilder < SDGUtils::DSL::ClassBuilder
      def self.in_sig?()       curr = self.get and curr.in_builder? end
      def self.in_sig_body?()  curr = self.get and curr.in_body? end

      def initialize(options={})
        super({
          :superclass => Alloy::Ast::Sig
        }.merge!(options))
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
      def sig(*args, &block)
        ans = build(*args, &block)
        for_each(ans) do |sig|
          ModelBuilder.in_model_body?           and
            mod = ModelBuilder.get.scope_module and
            mod.respond_to? :meta               and
            meta = mod.meta                     and
            meta.respond_to? :add_sig           and
            meta.add_sig(sig)
        end
        ans
      end

      protected

      def for_each(obj, &block)
        objs = (Array === obj) ? obj : [obj]
        objs.each &block
      end
    end

  end
end
