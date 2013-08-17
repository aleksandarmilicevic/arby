require 'alloy/alloy_ast'
require 'alloy/alloy_meta'
require 'sdg_utils/meta_utils'
require 'sdg_utils/dsl/module_builder'
require 'sdg_utils/dsl/class_builder'

module Alloy
  module DslEngine

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
          :mods_to_include => [Alloy::Dsl::Model]
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

    # ============================================================================
    # == Class ModBuilder
    #
    # Used to create expressions like
    #   +one/MyType+, +set/MyType+, etc.
    #
    # An object of this class is returned to represent
    # modifiers like "one", "set", "seq", etc, so that
    # +self/MyType+ and +self.MyType+ can result in an
    # instance of +Type+
    # ============================================================================
    class ModBuilder < BasicObject
      def /(other)
        ModBuilder.mult(@mod_smbl, other)
      end

      #------------------------------------------------------------------------
      # Creates an Alloy type with a multiplicity modifier assigned
      # +Alloy::Ast::ModType+ for a given multiplicity modifier and a given sig.
      #------------------------------------------------------------------------
      def self.mult(mod_smbl, *sig)
        if sig.empty?
          new(mod_smbl)
        else
          wrapped = sig[0]
          unless wrapped.kind_of? ::Alloy::Ast::AType
            wrapped = ::Alloy::Ast::UnaryType.new(sig[0])
          end
          ::Alloy::Ast::ModType.new(wrapped, mod_smbl)
        end
      end

      private

      def initialize(mod_smbl)
        @mod_smbl = mod_smbl
      end
    end

    # ============================================================================
    # == Class +SigBuilder+
    #
    # Used to create sig classes.
    # ============================================================================
    class SigBuilder < SDGUtils::DSL::ClassBuilder
      def initialize(options={})
        opts = {
          :superclass => Alloy::Ast::Sig,
          :builder_features => Alloy::Ast::ASig::Builder
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
