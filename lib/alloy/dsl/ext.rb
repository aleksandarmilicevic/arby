#TODO consider moving some of this stuff to sdg_utils/dsl

require 'alloy/alloy_ast'
require 'alloy/alloy_dsl'
require 'sdg_utils/dsl/ext'
require 'sdg_utils/meta_utils'
require 'sdg_utils/dsl/missing_builder'

def alloy_model_mgr() Alloy::Dsl::ModelBuilder.get end
def in_alloy_dsl?()   Alloy::Dsl::ModelBuilder.in_model? end
def allow_missing_consts_in_alloy_models?()
  ans = Alloy.conf.allow_undef_consts && in_alloy_dsl?
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
