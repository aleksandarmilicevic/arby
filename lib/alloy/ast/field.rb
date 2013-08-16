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
    class Field
      attr_reader :parent, :name, :type, :default, :inv, :impl, :synth

      class << self
        def getter_sym(fld)
          case fld
          when Alloy::Ast::Field
            fld.name.to_sym
          when String
            fld.to_sym
          when Symbol
            fld
          else
            msg = "`fld' must be in [Field, String, Symbol], but is #{fld.class}"
            raise ArgumentError, msg
          end
        end

        def setter_sym(fld)
          "#{getter_sym(fld)}=".to_sym
        end
      end

      # Hash keys:
      #   :parent [ASig]    - parent sig
      #   :name [String]    - name
      #   :type [AType]     - type
      #   :default [object] - default value
      #   :inv [Field]  - inv field
      #   :synth [Bool]     - whether synthesized of defined by the user
      #   :belongs_to_parent [Bool] - whether its value is owned by field's parent
      #   :transient [Bool] - whether it is transient (false by default)
      def initialize(hash)
        @parent  = hash[:parent]
        @name    = hash[:name]
        @type    = hash[:type]
        @default = hash[:default]
        set_inv(hash[:inv])
        @synth   = hash[:synth] || false
        @belongs_to_parent = hash[:belongs_to_parent] || hash[:owned] || false
        @transient = hash[:transient] || false
      end

      def scalar?()            @type.scalar? end
      def primitive?()         scalar? && @type.range.primitive? end
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

      def getter_sym() Field.getter_sym(self) end
      def setter_sym() Field.setter_sym(self) end

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
        full_name.gsub /[^a-zA-Z0-9_]/, "_"
      end

      protected

      def inv=(fld) @inv = fld end
    end

  end
end
