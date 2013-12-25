require 'arby/ast/field'
require 'arby/ast/sig'
require 'arby/ast/tuple_set'
require 'arby/ast/type_checker'

module Arby
  module Ast

    # Rel: [Class(Arby::Ast::Sig), Arby::Ast::Field, Arby::Ast::TypeConsts::Int]
    #
    # @attr sig_lowers, sig_uppers [Hash(Rel, Arby::Ast::TupleSet)]
    # @attr fld_lowers, fld_uppers [Hash(Rel, Arby::Ast::TupleSet)]
    class Bounds

      def initialize
        @lowers = {}
        @uppers = {}
      end

      def bound(what, lower, upper=nil)
        set_bound(@lowers, what, lower)
        set_bound(@uppers, what, upper || lower)
        self
      end

      def bound_exactly(what, tuple_set) bound(what, tuple_set, nil) end
      def bound_int(lower)               bound_exactly(TypeConsts::Int, lower) end

      def add_lower(what, tuple_set)
        add_bound(@lowers, what, tuple_set)
        add_bound(@uppers, what, tuple_set)
      end

      def add_upper(what, tuple_set)
        add_bound(@uppers, what, tuple_set)
      end

      def set_lower(what, tuple_set) set_bound(@lowers, what, tuple_set) end
      def set_upper(what, tuple_set) set_bound(@uppers, what, tuple_set) end

      def get_lower(what) @lowers[what] end #dup ???
      def get_upper(what) @uppers[what] end #dup ???

      private

      def set_bound(where, what, tuple_set)
        tuple_set = TupleSet.wrap(tuple_set)
        type = check_bound(what, tuple_set)
        ts = get_or_new(where, what, type)
        ts.clear!
        ts.union!(tuple_set)
        self
      end

      def add_bound(where, what, tuple_set)
        tuple_set = TupleSet.wrap(tuple_set)
        type = check_bound(what, tuple_set)
        ts = get_or_new(where, what, type)
        ts.union!(tuple_set)
        self
      end

      def check_bound(what, tuple_set)
        type = check_boundable(what)
        TypeChecker.check_subtype!(type, tuple_set._type)
        type
      end

      def get_or_new(col, what, type)
        col[what] ||= TupleSet.wrap([], type)
      end

      def check_boundable(what)
        case
        when Field === what                    then what.full_type
        when TypeChecker.check_sig_class(what) then what.to_atype
        when TypeConsts::Int == what           then TypeConsts::Int
        else
          raise TypeError, "only Field instances or Sig class can be bound; got #{what}"
        end
      end
    end

  end
end
