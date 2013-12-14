require 'arby/ast/sig'
require 'arby/ast/types'
require 'arby/ast/type_checker'
require 'arby/relations/relation'
require 'sdg_utils/proxy'

module Alloy
  module Ast

    module TypeMethodsHelper
      def add_methods_for_type()
        return unless @type
        cls = (class << self; self end)
        range_cls = @type.range.klass
        if (Alloy::Ast::ASig >= range_cls rescue false)
          fields = range_cls.meta.fields_including_sub_and_super
          # field += range_cls.meta.inv_fields_including_sub_and_super
          fields.each do |fld|
            fname = fld.getter_sym.to_s
            cls.send(:define_method, fname){ self._join_fld(fld) }
          end
        end
      end
    end

    class Tuple < SDGUtils::Proxy
      include Alloy::Relations::MTuple
      include TypeMethodsHelper

      private

      def initialize(type, atoms)
        atoms = Array(atoms) #TODO: fail if there are nils .reject(&:nil?)
        type ||= AType.get(atoms.map(&:class))
        TypeChecker.typecheck(type, atoms)
        super(atoms)
        # type.arity == 1 ? super(atoms.first) : super(atoms)
        @type = type
        @atoms = atoms
        add_methods_for_type
      end

      public

      def self.wrap(t, type=nil)
        case t
        when Tuple then t
        else
          Tuple.new(type, t)
        end
      end

      def unwrap()  TupleSet.unwrap(self) end
      def atoms()   @atoms.dup() end
      def atom(idx) @atoms[idx] end

      def _target() @target end
      def _type()   @type end

      def _join_fld(fld)
        fname = fld.getter_sym.to_s
        rhs = self.atoms.last
        ans = rhs ? (atoms[0...-1] + [rhs.send(fname)]) : nil
        Tuple.new(@type.join(fld.full_type()), ans)
      end

      def to_s()    "<" + @atoms.map(&:to_s).join(", ") + ">" end
      def inspect() to_s end
    end

    ###############################################

    class TupleSet < SDGUtils::Proxy
      include Alloy::Relations::MRelation
      include TypeMethodsHelper

      private

      def initialize(type, tuples)
        tuples = Array(tuples)
        @tuples = Set.new(tuples.map{|t| Tuple.wrap(t, type)}.reject(&:empty?))
        @type = type || AType.interpolate(@tuples.map(&:_type))
        TypeChecker.assert_type(@type)
        super(@tuples)
        # (type.scalar?) ? super(@tuples.first) : super(@tuples)
        add_methods_for_type
      end

      public

      def self.wrap(t, type=nil)
        case t
        when TupleSet then t
        else
          TupleSet.new(type, t)
        end
      end

      def self.unwrap(t)
        case t
        when TupleSet   then self.unwrap(t._target)
        when Tuple then self.unwrap(t._target)
        when Array      then t.map{|e| self.unwrap(e)}
        when Set        then Set.new(t.map{|e| self.unwrap(e)})
        else
          t
        end
      end

      def _target()    @target end
      def _type()      @type end

      def arity()      @type.arity end
      def tuples()     @tuples.dup end
      def unwrap()     TupleSet.unwrap(self) end
      def size()       tuples.size end
      def empty?()     tuples.empty? end
      def join(*a, &b) tuples.join(*a, &b) end
      def contains?(a) a.all?{|e| tuples.member?(e)} end

      def <(other)     int_cmp(:<, other) end
      def >(other)     int_cmp(:>, other) end
      def <=(other)    int_cmp(:<=, other) end
      def >=(other)    int_cmp(:>=, other) end

      def sum
        assert_int_set!
        @tuples.reduce(0){|sum, t| sum + t[0]}
      end

      def hash()    TupleSet.unwrap(self).hash end
      def ==(other) TupleSet.unwrap(self) == TupleSet.unwrap(other) end

      def to_s()    "{" + @tuples.map(&:to_s).join(",\n  ") + "}" end
      def inspect() to_s end

      def assert_int_set!
        unless @type && @type.isInt?
          raise TypeError, "#{self} must be an integer value to be able to apply #{op};"+
            "instead, its type is #{@type}"
        end
      end

      private

      def int_cmp(op, other)
        self.sum.send(op, TupleSet.wrap(other).sum)
      end

      def _wrap(result)
        TupleSet.new(@type, result)
      end

      def _join_fld(fld)
        fname = fld.getter_sym.to_s
        ans = self.tuples.map(&fname).reject(&:no?)
        TupleSet.new(@type.join(fld.full_type()), ans)
      end
    end

  end
end
