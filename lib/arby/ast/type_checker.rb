require 'arby/alloy_conf'
require 'arby/ast/types'
require 'sdg_utils/errors'

module Arby
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

      def check_subtype(expected, actual)
        Class === expected &&
          Class === actual &&
          actual <= expected #TODO: incomplete
      end

      # @param type - anything that can be converted to +AType+ via +AType.get+
      # @param tuple [Array]
      def typecheck!(type, tuple)
        atype = AType.get(type)
        tuple = Array(tuple)
        msg = "tuple #{tuple} doesn't typecheck against #{atype}"
        raise TypeError, "arities differ: #{msg}" unless atype.arity == tuple.size
        raise TypeError, msg unless atype === tuple
      end

      def assert_type!(type)
        raise TypeError, "no type given: #{type}" unless AType === type && type.arity > 0
      end

      def typecheck(type, tuple) Arby.conf.typecheck and typecheck!(type, tuple) end
      def assert_type(type)      Arby.conf.typecheck and assert_type!(type) end

      def check_sig_class(cls, supercls=Arby::Ast::ASig, msg="")
        msg = "#{msg}\n" unless msg.to_s.empty?
        raise_not_sig = proc {
          raise TypeError, "#{msg}#{cls} is not a #{supercls} class"
        }
        raise_not_sig[] unless Class === cls
        raise_not_sig[] unless cls < supercls
      end

      def check_alloy_module(mod, msg="")
        msg = "#{msg}\n" unless msg.to_s.empty?
        raise_not_mod = proc {
          raise TypeError, "#{msg}#{mod} is not a ruby module used as Alloy model"
        }
        raise_not_mod[] unless Module === mod
        raise_not_mod[] unless mod.respond_to? :meta
        raise_not_mod[] unless Arby::Ast::Model === mod.meta
        mod.meta
      end
    end

  end
end
