require 'alloy/ast/types'

module Alloy
  module Dsl

    # ============================================================================
    # == Class ModBuilder
    #
    # Used to create expressions like +one/MyType+, +set/MyType+, etc.
    #
    # An object of this class is returned to represent modifiers like
    # "one", "set", "seq", etc, so that +self/MyType+ and
    # +self.MyType+ can result in an instance of +Type+
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
          unless ::Alloy::Ast::AType === wrapped
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

  end
end
