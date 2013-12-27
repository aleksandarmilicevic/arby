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

      # @return [Array] - list of all atoms appearing in all the bounds
      def extract_universe
        univ = Set.new
        entries do |_, what, ts|
          t = type_for_boundable(what)
          unless t.all?(&:primitive?)
            univ += ts.tuples!.map(&:atoms!).flatten
          end
        end
        univ.to_a
      end

      def serialize
        @universe = extract_universe
        @atom2label = {}

        # label atoms to make sure all of them have labels
        # in the format of '<sig_name>$<index>'
        @universe.group_by(&:class).each do |cls, atoms|
          cls_name = cls <= Integer ? "Int" : cls.relative_name
          atoms.each_with_index{|a, idx| @atom2label[a] = "#{cls_name}$#{idx}"}
        end

        t_to_s =  proc{|t|  "<" + t.map{|a| @atom2label[a]}.join(', ') + ">"}
        ts_to_s = proc{|ts| "{" + ts.map{|t| t_to_s[t]}.join('') + "}"}

        bounds_to_str = proc{|prefix, var|
          var.map{ |what, ts|
            if what == Arby::Ast::TypeConsts::Int
              nil
            else
              what_name = case what
                          when Class then what.relative_name
                          when Field then what.full_relative_name
                          else what.to_s
                          end
              "#{prefix}[#{what_name}] = #{ts_to_s[ts]}"
            end
          }.compact.join("\n")
        }
        """
universe = #{t_to_s[@universe]}
#{bounds_to_str[:lowers, @lowers]}
#{bounds_to_str[:uppers, @uppers]}
"""
      end

      private

      def entries
        @lowers.each{|what, ts| yield(:lowers, what, ts)}
        @uppers.each{|what, ts| yield(:uppers, what, ts)}
      end

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

      def type_for_boundable(what)
        case
        when Field === what                    then what.full_type
        when TypeChecker.check_sig_class(what) then what.to_atype
        when TypeConsts::Int == what           then TypeConsts::Int
        else
          nil
        end
      end

      def check_boundable(what)
        type_for_boundable(what) or (
          msg = "`#{what}' not boundable (expected Field, Class<Sig>, or AType<Int>)" and
          raise(TypeError, msg))
      end
    end

  end
end
