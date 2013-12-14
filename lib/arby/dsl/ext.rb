#TODO consider moving some of this stuff to sdg_utils/dsl

require 'arby/alloy_ast'
require 'arby/alloy_dsl'
require 'arby/ast/types'
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
      # Converts self to +Arby::Ast::UnaryType+ and then delegates
      # the +*+ operation to it.
      #
      # @see Arby::Ast::AType
      # @see Arby::Ast::UnaryType
      # @see Arby::Ast::ProductType
      #--------------------------------------------------------
      def *(rhs) ::Arby::Ast::AType.get(self) * rhs end
      def **(rhs) ::Arby::Ast::AType.get(self) ** rhs end
    end
  end
end

#--------------------------------------------------------
# == Extensions to class +Class+
#--------------------------------------------------------
class Class
  #--------------------------------------------------------
  # Converts this class to +Arby::Ast::UnaryType+ and
  # then delegates the +*+ operation to it.
  #
  # @see Arby::Ast::AType
  # @see Arby::Ast::UnaryType
  # @see Arby::Ast::ProductType
  #--------------------------------------------------------
  def *(rhs)  to_atype * rhs end
  def **(rhs) to_atype ** rhs end

  def set_of()   Arby::Dsl::MultHelper.set(self) end
  def is_sig?()  ancestors.member? Arby::Ast::ASig end
  def to_atype() Arby::Ast::AType.get(self) end
end

class Object
  def to_atype() Arby::Ast::AType.get(self) end
end
