require 'sdg_utils/meta_utils'
require 'sdg_utils/dsl/missing_builder'

def model_mgr() SDGUtils::DSL::ModuleBuilder.get end
def in_dsl?()   SDGUtils::DSL::BaseBuilder.in_builder? end


module SDGUtils
  module DSL
    module Ext
      # --------------------------------------------------------
      # Catches all +const_missing+ events, so that, only when
      # evaluating in the context of Dsl, instead of failing it simply
      # wraps it in a SDGUtils::DSL::MissingBuilder object.
      # --------------------------------------------------------
      def self.my_const_missing(sym)
        # first try to find in the current module
        begin
          mod = model_mgr.scope_module
          if mod.const_defined?(sym, false)
            mod.const_get(sym)
          else
            MissingBuilder.new sym
          end
        rescue(NameError)
          # if not found in the module, return MisingBuilder
          MissingBuilder.new sym
        end
      end
    end
  end
end

#--------------------------------------------------------
# == Extensions to class +Module+
#--------------------------------------------------------
class << Object
  alias_method :old_const_missing, :const_missing

  def const_missing(sym)
    return super unless in_dsl?
    SDGUtils::DSL::Ext.my_const_missing(sym)
  end
end

class Module
  alias_method :old_const_missing, :const_missing

  def const_missing(sym)
    begin
      return super unless in_dsl?
    rescue
      raise "Constant #{sym} not found in module #{self}"
    end
    SDGUtils::DSL::Ext.my_const_missing(sym)
  end
end

#--------------------------------------------------------
# == Extensions to class +Class+
#--------------------------------------------------------
class Module
  #--------------------------------------------------------------------
  # Helper method that returns the name of the module which this class
  # was defined in (where everything after and including the last
  # appearance of '::' is stripped out).
  # -------------------------------------------------------------------
  def module_name
    to_s.module_name
  end

  #--------------------------------------------------------
  # Helper method that returns the relative (i.e., simple) name of
  # this class (where all module name prefixes are stripped out).
  #--------------------------------------------------------
  def relative_name
    to_s.relative_name
  end
end

#--------------------------------------------------------
# == Extensions to class +String+
#--------------------------------------------------------
class String
  alias_method :old_cmp, :<

  #-----------------------------------------------------------------
  # Overrides the +<+ operator so that, when in Dsl context and the
  # +rhs+ operand is of type +Class+, it returns a +[self, rhs]+ tuple
  # so that the context can interpret it as sig extension.
  #
  # @see String#<
  #-----------------------------------------------------------------
  def <(rhs)
    return old_cmp rhs unless in_dsl?
    case rhs
    when Class
      [self, rhs]
    else
      old_cmp rhs
    end
  end

  def split_to_module_and_relative
    sp = split('::')
    [sp[0..-2].join('::'), sp.last]
  end

  #---------------------------------------------------------------
  # Strips out everything after the last appearance of '::'.
  #---------------------------------------------------------------
  def module_name
    split_to_module_and_relative[0]
  end

  #--------------------------------------------------------
  # Strips out everything but the substring after the last
  # appearance of '::'.
  #--------------------------------------------------------
  def relative_name
    split_to_module_and_relative[1]
  end
end

#--------------------------------------------------------
# == Extensions to class +Symbol+
#--------------------------------------------------------
class Symbol
  alias_method :old_cmp, :<

  #---------------------------------------------------------------
  # Overrides the +<+ operator so that, when in Dsl context and the
  # +rhs+ operand is of type +Class+, it returns a +[self, rhs]+ tuple
  # so that the context can interpret it as sig extension.
  #
  # @see String#<
  #----------------------------------------------------------------
  def <(rhs)
    return old_cmp rhs unless in_dsl?
    SDGUtils::DSL::MissingBuilder.new(self) < rhs
  end
end

