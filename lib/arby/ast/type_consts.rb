require 'arby/ast/types'

module Arby
  module Ast

    module SigConsts
      class UnivCls
        def self.relative_name() "univ" end
      end
    end

    module TypeConsts
      extend self

      Univ  = UnaryType.new(SigConsts::UnivCls)
      Univ1 = Univ
      Int   = UnaryType.new(Integer)
      Bool  = UnaryType.new(:Bool)
      Seq   = ProductType.new(Int, Univ)

      def Int() TypeConsts::Int end

      def self.get(sym)
        case sym.to_s
        when "Int", "Integer" then Int
        when "seq/Int"        then Int
        else
          nil
        end
      end

      def self.get!(sym) self.get(sym) or TypeError.raise_type_coercion_error(sym) end
    end

  end
end
