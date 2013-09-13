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
        # special case for missing builder with appended facts block
        fst = args.first
        ans =
          if SDGUtils::DSL::MissingBuilder === fst && fst.has_body?
            body = fst.remove_body
            ans = build(*args, &block)
            return_result(:array).first.send :fact, &body
            ans
          else
            build(*args, &block)
          end
        return_result(:array).each do |sig|
          ModelBuilder.in_model_body?           and
            mod = ModelBuilder.get.scope_module and
            mod.respond_to? :meta               and
            meta = mod.meta                     and
            meta.respond_to? :add_sig           and
            meta.add_sig(sig)
        end
        ans
      end
    end

  end
end
