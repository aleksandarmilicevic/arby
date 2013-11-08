#TODO consider moving some of this stuff to sdg_utils/dsl

require 'alloy/alloy_ast'
require 'alloy/alloy_dsl'
require 'alloy/ast/types'
require 'sdg_utils/dsl/ext'
require 'sdg_utils/meta_utils'
require 'sdg_utils/dsl/missing_builder'

#--------------------------------------------------------
# == Extensions to class +SDGUtils::DSL::MissingBuilder+
#--------------------------------------------------------
module SDGUtils
  module DSL
    class MissingBuilder
      #--------------------------------------------------------
      # Converts self to +Alloy::Ast::UnaryType+ and then delegates
      # the +*+ operation to it.
      #
      # @see Alloy::Ast::AType
      # @see Alloy::Ast::UnaryType
      # @see Alloy::Ast::ProductType
      #--------------------------------------------------------
      def *(rhs)
        ::Alloy::Ast::UnaryType.new(self) * rhs
      end
    end
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
  def **(rhs)
    to_atype * rhs
  end

  def set_of()   Alloy::Dsl::MultHelper.set(self) end
  def is_sig?()  ancestors.member? Alloy::Ast::ASig end
  def to_atype() Alloy::Ast::UnaryType.new(self) end
end
