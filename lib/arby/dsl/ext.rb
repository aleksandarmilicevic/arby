#TODO consider moving some of this stuff to sdg_utils/dsl

require 'arby/arby_ast'
require 'arby/arby_dsl'
require 'arby/ast/types'
require 'arby/ast/scope'
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
      def *(rhs) ::Arby::Ast::AType.get!(self) * rhs end
      def **(rhs) ::Arby::Ast::AType.get!(self) ** rhs end
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
  def to_atype() Arby::Ast::AType.get!(self) end
end

class Fixnum
  def exactly
    Arby::Ast::SigScope.new(nil, self, true)
  end
end

class Array
  def *(rhs) Arby::Ast::TupleSet.wrap(self) * rhs end
  def **(rhs) Arby::Ast::TupleSet.wrap(self) ** rhs end
end


class Object
  def to_atype() Arby::Ast::AType.get(self) end
end

class Range
  def to_tuple_set
    require 'arby/ast/tuple_set'
    Arby::Ast::TupleSet.wrap(self)
  end


  def self.delegate_to_ts(*syms)
    syms.each do |sym|
      self.send :define_method, sym do |*a, &b|
        to_tuple_set.send sym, *a, &b
      end
    end
  end

  delegate_to_ts :*, :**, :product, :union, :join
end
