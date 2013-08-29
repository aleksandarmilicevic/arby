require 'sdg_utils/errors'

module Alloy
  module Ast

    #-----------------------------------------------------
    # == Class +TypeError+
    #
    # Raised in case of various type errors (e.g., trying
    # to extend a sig from the +String+ class).
    #-----------------------------------------------------
    class TypeError < StandardError
    end

    class ResolveError < StandardError
    end


    #-----------------------------------------------------
    # == Class +TypeChecker+
    #-----------------------------------------------------
    module TypeChecker
      extend self

      def check_type(expected, actual)
        actual <= expected #TODO: incomplete
      end

      def check_sig_class(cls)
        raise_not_sig = proc{raise TypeError, "#{cls} is not a sig class"}
        raise_not_sig[] unless Class === cls
        raise_not_sig[] unless cls < Alloy::Ast::ASig
      end

      def check_alloy_module(mod)
        raise_not_mod = proc{
          raise TypeError, "#{mod} is not a ruby module used as Alloy model"
        }
        raise_not_mod[] unless Module === mod
        raise_not_mod[] unless mod.respond_to? :meta
        raise_not_mod[] unless Alloy::Ast::Model === mod.meta
      end
    end

  end
end
