require 'alloy/ast/arg'
require 'sdg_utils/string_utils'

 module Alloy
  module Ast

    # ----------------------------------------------------------------------
    # Holds meta information about a field of a sig.
    #
    # @attr parent [Class <= ASig]
    # @attr name [String]
    # @attr type [AType]
    # @attr inv [Field]
    # @attr impl [Field, Proc: Field]
    # @attr synt [TrueClass, FalseClass]
    # @attr belongs_to_parent [TrueClass, FalseClass]
    # @immutable
    # ----------------------------------------------------------------------
    class Field < Arg
      attr_reader   :parent, :inv, :impl, :synth
      attr_accessor :default

      def self.getter_sym(fld) Arg.getter_sym(fld) end
      def self.setter_sym(fld) Arg.setter_sym(fld) end

      # Hash keys:
      #   :parent [ASig]            - parent sig
      #   :name [String]            - name
      #   :type [AType]             - type
      #   :default [object]         - default value
      #   :inv [Field]              - inv field
      #   :synth [Bool]             - whether synthesized of defined by the user
      #   :belongs_to_parent [Bool] - whether its value is owned by field's parent
      #   :transient [Bool]         - whether it is transient (false by default)
      def initialize(hash)
        super(hash)
        @parent            = hash[:parent]
        @default           = hash[:default]
        @synth             = hash[:synth] || false
        @belongs_to_parent = hash[:belongs_to_parent] || hash[:owned] || false
        @transient         = hash[:transient] || false
        set_inv(hash[:inv])
      end

      def getter_sym()         Field.getter_sym(self) end
      def setter_sym()         Field.setter_sym(self) end

      def transient?()         @transient end
      def persistent?()        !@transient end
      def synth?()             @synth end
      def is_inv?()            @synth && !!@inv && !@inv.synth? end
      def set_inv(invfld)      @inv = invfld; invfld.inv=self unless invfld.nil? end
      def set_impl(impl)       @impl = impl end
      def set_synth()          @synth = true end
      def has_impl?()          !!@impl end
      def impl()               Proc === @impl ? @impl.call : @impl end
      def belongs_to_parent?() !!@belongs_to_parent end

      def full_name() "#{@parent.name}.#{name}" end
      def full_type() Alloy::Ast::ProductType.new(@parent.to_atype, @type) end

      # @param owner [Alloy::Ast::ASig]
      # @param value [Object]
      def set(owner, value)
        owner.write_field(self, value)
      end

      def to_s()
        ret = full_name
        ret = "transient " + ret if transient?
        ret = "synth " + ret if synth?
        ret
      end

      def to_alloy
        decl = "#{name.to_s}: #{type.to_alloy}"
        @synth ? "~#{decl}" : decl
      end

      def to_iden
        SDGUtils::StringUtils.to_iden(full_name)
      end

      def to_alloy_expr()
        if is_inv?
          e = Expr::UnaryExpr.transpose Expr::FieldExpr.new(self.inv)
          Expr.add_methods_for_type(e, self.inv.full_type.transpose)
          e
        else
          Expr::FieldExpr.new(self)
        end
      end

      protected

      def inv=(fld) @inv = fld end
    end

  end
end
