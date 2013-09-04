#TODO consider moving some of this stuff to sdg_utils/dsl

require 'alloy/alloy_ast'
require 'alloy/alloy_dsl'
require 'sdg_utils/meta_utils'
require 'sdg_utils/dsl/missing_builder'

def alloy_model_mgr() Alloy::Dsl::ModelBuilder.get end
def in_alloy_dsl?()   Alloy::Dsl::ModelBuilder.in_model? end
def allow_missing_consts_in_alloy_models?()
  ans = Alloy.conf.allow_undef_consts && in_alloy_dsl?
end

module Alloy
  module Dsl
    module Ext
      # --------------------------------------------------------
      # Catches all +const_missing+ events, so that, only when
      # evaluating in the context of Alloy Dsl, instead of failing it
      # simply wraps it in a SDGUtils::DSL::MissingBuilder object.
      # --------------------------------------------------------
      def self.my_const_missing(sym)
        # first try to find in the current module
        begin
          mod = alloy_model_mgr.scope_module
          if mod.const_defined?(sym, false)
            mod.const_get(sym)
          else
            SDGUtils::DSL::MissingBuilder.new sym
          end
        rescue(NameError)
          # if not found in the module, return MisingConst
          SDGUtils::DSL::MissingBuilder.new sym
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
    return super unless allow_missing_consts_in_alloy_models?
    Alloy::Dsl::Ext.my_const_missing(sym)
  end
end

class Module
  alias_method :old_const_missing, :const_missing

  def const_missing(sym)
    begin
      return super unless allow_missing_consts_in_alloy_models?
    rescue
      raise "Constant #{sym} not found in module #{self}"
    end
    Alloy::Dsl::Ext.my_const_missing(sym)
  end
end

#--------------------------------------------------------
# == Extensions to class +Class+
#--------------------------------------------------------
class Class
  #--------------------------------------------------------
  # Converts this class to +Alloy::Ast::UnaryType+ and
  # then delegates the +*+ operation to it.
  #
  # @see Alloy::Ast::AType
  # @see Alloy::Ast::UnaryType
  # @see Alloy::Ast::ProductType
  #--------------------------------------------------------
  def *(rhs)
    to_atype * rhs
  end

  def set_of()   Alloy::Dsl::MultHelper.set(self) end
  def is_sig?()  ancestors.member? Alloy::Ast::ASig end
  def to_atype() Alloy::Ast::UnaryType.new(self) end
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

  #--------------------------------------------------------
  # Overrides the +<+ operator so that, when in Alloy Dsl
  # context and the +rhs+ operand is of type +Class+, it
  # returns a +[self, rhs]+ tuple so that the context
  # can interpret it as sig extension.
  #
  # @see String#<
  #--------------------------------------------------------
  def <(rhs)
    return old_cmp rhs unless in_alloy_dsl?
    case rhs
    when Class
      # Alloy::Dsl::NameSuperclassPair.new(self, rhs)
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

  #--------------------------------------------------------
  # Overrides the +<+ operator so that, when in Alloy Dsl
  # context and the +rhs+ operand is of type +Class+, it
  # returns a +[self, rhs]+ tuple so that the context
  # can interpret it as sig extension.
  #
  # @see String#<
  #--------------------------------------------------------
  def <(rhs)
    return old_cmp rhs unless in_alloy_dsl?
    case rhs
    when Class, Symbol
      [self, rhs]
    else
      old_cmp rhs
    end
  end
end

class Object
  def get_module
    if [Class, Module].include? self.class
      self
    else
      self.class
    end
  end
end

