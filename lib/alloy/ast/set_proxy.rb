require 'alloy/ast/sig'
require 'alloy/ast/type_checker'
require 'alloy/relations/relation'
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

    class TupleProxy < SDGUtils::Proxy
      include Alloy::Relations::MTuple
      include TypeMethodsHelper

      private

      def initialize(type, atoms)
        atoms = Array(atoms).reject(&:nil?)
        unless type.arity == atoms.size
          msg = "The number of #{atoms.size} atoms (#{atoms}) doesn't match " +
            "given type's (#{type}) arity (#{type.arity})"
          raise TypeError, msg
        end
        super(atoms)
        # type.arity == 1 ? super(atoms.first) : super(atoms)
        @type = type
        @atoms = atoms
        add_methods_for_type
      end

      public

      def self.wrap(type, t)
        case t
        when TupleProxy then t
        else
          TupleProxy.new(type, t)
        end
      end

      def unwrap() SetProxy.unwrap(self) end
      def values() @atoms.dup() end

      def _target() @target end
      def _type()   @type end

      def _join_fld(fld)
        fname = fld.getter_sym.to_s
        rhs = self.atoms.last
        ans = rhs ? (atoms[0...-1] + [rhs.send(fname)]) : nil
        TupleProxy.new(@type.join(fld.full_type()), ans)
      end

      def to_s()    "<" + @atoms.map(&:to_s).join(", ") + ">" end
      def inspect() to_s end
    end

    ###############################################

    class SetProxy < SDGUtils::Proxy
      include Alloy::Relations::MRelation
      include TypeMethodsHelper

      private

      def initialize(type, tuples)
        tuples = Array(tuples)
        @tuples = Set.new(tuples.map{|t| TupleProxy.wrap(type, t)}.reject(&:empty?))
        @type = type
        super(@tuples)
        # (type.scalar?) ? super(@tuples.first) : super(@tuples)
        add_methods_for_type
      end

      public

      def self.wrap(type, t)
        case t
        when SetProxy then t
        else
          SetProxy.new(type, t)
        end
      end

      def self.unwrap(t)
        case t
        when SetProxy   then self.unwrap(t._target)
        when TupleProxy then self.unwrap(t._target)
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
      def unwrap()     SetProxy.unwrap(self) end
      def map(*a, &b)  tuples.map(*a, &b) end
      def size()       tuples.size end
      def empty?()     tuples.empty? end
      def reject(&b)   delegate_and_wrap(:reject, &b) end
      def map(&b   )   delegate_and_wrap(:map, &b) end
      def compact(&b)  delegate_and_wrap(:compact, &b) end
      def join(*a, &b) tuples.join(*a, &b) end
      def contains?(a) a.all?{|e| tuples.member?(e)} end

      def hash()    SetProxy.unwrap(self).hash end
      def ==(other) SetProxy.unwrap(self) == SetProxy.unwrap(other) end

      def to_s()    "{" + @tuples.map(&:to_s).join(",\n  ") + "}" end
      def inspect() to_s end

      private

      def delegate_and_wrap(func_sym, *a, &b)
        _wrap(tuples.send(func_sym, *a, &b))
      end

      def _wrap(result)
        SetProxy.new(@type, result)
      end

      def _join_fld(fld)
        fname = fld.getter_sym.to_s
        ans = self.tuples.map(&fname).reject(&:no?)
        SetProxy.new(@type.join(fld.full_type()), ans)
      end
    end

  end
end
