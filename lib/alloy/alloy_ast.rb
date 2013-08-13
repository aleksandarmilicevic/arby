require 'alloy/alloy_ast_errors.rb'
require 'alloy/alloy_conf.rb'
require 'alloy/alloy_dsl.rb'
require 'alloy/alloy_event_constants.rb'
require 'alloy/utils/codegen_repo'
require 'sdg_utils/meta_utils'
require 'date'

module Alloy
  module Ast

    # ----------------------------------------------------------------------
    # Holds meta information about a field of a sig.
    #
    # @attr parent [Class <= ASig]
    # @attr name [String]
    # @attr type [AType]
    # @attr inv [FieldMeta]
    # @attr impl [FieldMeta, Proc: FieldMeta]
    # @attr synt [TrueClass, FalseClass]
    # @attr belongs_to_parent [TrueClass, FalseClass]
    # @immutable
    # ----------------------------------------------------------------------
    class FieldMeta
      attr_reader :parent, :name, :type, :default, :inv, :impl, :synth

      class << self
        def getter_sym(fld)
          case fld
          when Alloy::Ast::FieldMeta
            fld.name.to_sym
          when String
            fld.to_sym
          when Symbol
            fld
          else
            msg = "`fld' must be in [FieldMeta, String, Symbol], but is #{fld.class}"
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
      #   :inv [FieldMeta]  - inv field
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

      def getter_sym() FieldMeta.getter_sym(self) end
      def setter_sym() FieldMeta.setter_sym(self) end

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

    # ----------------------------------------------------------------------
    # Holds meta information (e.g., fields and their types) about
    # a sig class.
    #
    # @attr sig_cls    [Class <= Sig]
    # @attr subsigs    [Array(Class <= Sig)]
    # @attr fields     [Array(FieldMeta)]
    # @attr inv_fields [Array(FieldMeta)]
    # ----------------------------------------------------------------------
    class SigMeta
      attr_reader :sig_cls, :parent_sig
      attr_reader :abstract, :placeholder
      attr_reader :subsigs
      attr_reader :fields, :inv_fields
      attr_reader :extra

      def initialize(sig_cls, placeholder=false, abstract=false)
        @sig_cls = sig_cls
        @parent_sig = sig_cls.superclass if (sig_cls.superclass.is_sig? rescue nil)
        @placeholder = placeholder
        @abstract = abstract
        @subsigs = []
        @fields = []
        @inv_fields = []
        @extra = {}
      end

      def abstract?;       @abstract end
      def set_abstract;    @abstract = true end
      def placeholder?;    @placeholder end
      def set_placeholder; @placeholder = true end

      def persistent_fields(*args)
        fields(*args).select { |f| f.persistent? }
      end

      def transient_fields(*args)
        fields(*args).select { |f| f.transient? }
      end

      alias_method :pfields, :persistent_fields
      alias_method :tfields, :transient_fields

      def fields(include_inherited=false)
        ret=[] + @fields
        if include_inherited && parent_sig
          ret += parent_sig.meta.fields(true)
        end
        ret
      end

      def inv_fields(include_inherited=false)
        ret=[] + @inv_fields
        if include_inherited && parent_sig
          ret += parent_sig.meta.inv_fields(true)
        end
        ret
      end

      def all_fields(include_inherited=false)
        fields(include_inherited) + inv_fields(include_inherited)
      end

      def add_subsig(subsig_cls)
        @subsigs << subsig_cls
      end

      def all_subsigs
        @subsigs.map {|s| [s] << s.all_subsigs}.flatten
      end

      def all_supersigs
        if parent_sig
          [parent_sig] + parent_sig.meta.all_supersigs
        else
          []
        end
      end

      def oldest_ancestor(ignore_abstract=false, ignore_placeholder=true)
        if parent_sig
          parent_sig.oldest_ancestor(ignore_abstract) ||
            begin
              if ignore_placeholder && parent_sig.placeholder?
                nil
              elsif ignore_abstract && parent_sig.abstract?
                nil
              else
                parent_sig
              end
            end
        else
          nil
        end
      end

      def add_field(fld_name, fld_type, hash={})
        opts = hash.merge :parent => sig_cls,
                          :name   => fld_name.to_s,
                          :type   => fld_type
        fld = FieldMeta.new opts
        @fields << fld
        fld
      end

      def add_inv_field_for(f)
        full_inv_type = ProductType.new(f.parent.to_atype, f.type).inv
        if full_inv_type.domain.klass != @sig_cls
          raise ArgumentError, "Field #{f} doesn't seem to belong in class #{@sig_cls}"
        end
        # full_inv_type = ProductType.new(f.parent.to_atype, f.type).inv
        # raise ArgumentError if full_inv_type.column(0).cls.klass != @sig_cls
        inv_fld = FieldMeta.new :parent => @sig_cls,
                                :name   => Alloy.conf.inv_field_namer.call(f),
                                :type   => full_inv_type.full_range,
                                :inv    => f,
                                :synth  => true
        # f.set_inv(inv_fld)
        @inv_fields << inv_fld
        inv_fld
      end

      def field(fname, own_only=false)      find_in(fields(!own_only), fname) end
      def field!(fname, own_only=false)     find_in!(fields(!own_only), fname) end
      def [](sym)                           field(sym.to_s) end
      def inv_field(fname, own_only=false)  find_in(inv_fields(!own_only), fname) end
      def inv_field!(fname, own_only=false) find_in!(inv_fields(!own_only), fname) end

      def find_in(fld_ary, fname)
        #TODO cache?
        fld_ary.find {|f| f.name == fname.to_s}
      end

      def find_in!(fld_ary, fname, msg=nil)
        ret = find_in(fld_ary, fname)
        msg = (msg ? msg : "") + "`#{fname}' not found in #{fld_ary.map{|e| e.name}}"
        raise ArgumentError, msg unless ret
        ret
      end

      # Returns type associated with the given field
      #
      # @param fld [String, Symbol]
      # @return [AType]
      def field_type(fname)
        field(fname).type
      end

      # returns a string representation of the field definitions
      def fields_to_alloy; fld_list_to_alloy @fields  end

      # returns a string representation of the synthesized inv field definitions
      def inv_fields_to_alloy; fld_list_to_alloy @inv_fields end

      private

      def fld_list_to_alloy(flds)
        flds.map {|f| "  " + f.to_alloy }
            .join(",\n")
      end

    end

    #------------------------------------------
    # == Module ASig::Static
    #------------------------------------------
    module ASig
      module Static
        def inherited(subclass)
          super
          fail "The +meta+ method hasn't been defined for class #{self}" unless meta
          subclass.start
          meta.add_subsig(subclass)
        end

        def created()
          require_relative 'alloy.rb'
          Alloy.meta.sig_created(self)
        end

        def method_missing(sym, *args, &block)
          if args.empty? && block.nil?
            fld = meta.field(sym) || meta.inv_field(sym)
            if fld
              fld_mth = (fld.is_inv?) ? "inv_field" : "field"
              self.instance_eval <<-RUBY, __FILE__, __LINE__+1
                def #{sym}()
                  meta.#{fld_mth}(#{sym.inspect})
                end
              RUBY
              return fld
            else
              super
            end
          end
        end

        #------------------------------------------------------------------------
        # Class method for defining fields inside a class definition
        #------------------------------------------------------------------------
        def fields(hash={}, &block)
          _traverse_fields hash, lambda { |name, type| field(name, type) }, &block
        end

        alias_method :persistent, :fields
        alias_method :refs, :fields

        def owns(hash={}, &block)
          _traverse_fields hash, lambda { |name, type|
            field(name, type, :owned => true)
          }, &block
        end

        def transient(hash={}, &block)
          _traverse_fields hash, lambda { |name, type|
            field(name, type, :transient => true)
          }, &block
        end

        def field(*args)
          _traverse_field_args(args, lambda {|name, type, hash={}|
                                 _field(name, type, hash)})
        end

        alias_method :ref, :field

        #------------------------------------------------------------------------
        # For a given field (name, type) creates a getter and a setter
        # (instance) method, and adds it to this sig's +meta+ instance.
        #
        # @param fld_name [String]
        # @param fld_type [AType]
        #------------------------------------------------------------------------
        def _field(name, type, hash={})
          unless type.kind_of? Alloy::Ast::AType
            type = Alloy::Ast::AType.get(type)
          end
          fld = meta.add_field(name, type, hash)
          fld_accessors fld
          fld
        end

        def synth_field(name, type)
          field(name, type, :synth => true)
        end

        def abstract; _set_abstract; self end
        def placeholder; _set_placeholder; self end

        def invariant(&block)
          define_method(:invariant, &block)
        end

        # @see +SigMeta#abstract?+
        # @return [TrueClass, FalseClass]
        def abstract?; meta.abstract? end

        # @see +SigMeta#placeholder?+
        # @return [TrueClass, FalseClass]
        def placeholder?; meta.placeholder? end

        # @see +SigMeta#ignore_abstract+
        # @return [Class, NilClass]
        def oldest_ancestor(ignore_abstract=false)
          meta.oldest_ancestor(ignore_abstract)
        end

        # Returns highest non-placeholder ancestor of +self+ in the
        # inheritance hierarchy or self.
        def alloy_root
          meta.oldest_ancestor(false) || self
        end

        def all_supersigs()  meta.all_supersigs end
        def all_subsigs()  meta.all_subsigs end

        #------------------------------------------------------------------------
        # Defines a getter method for a field with the given symbol +sym+
        #------------------------------------------------------------------------
        def fld_accessors(fld)
          cls = Module.new
          fld_sym = fld.getter_sym
          find_fld_src = if fld.is_inv?
                           "meta.inv_field!(#{fld_sym.inspect})"
                         else
                           "meta.field!(#{fld_sym.inspect})"
                         end
          desc = {
            :kind => :fld_accessors,
            :target => self,
            :field => fld_sym
          }
          Alloy::Utils::CodegenRepo.eval_code cls, <<-RUBY, __FILE__, __LINE__+1, desc
def #{fld_sym}
  intercept_read(#{find_fld_src}){
    #{_fld_reader_code(fld)}
  }
end
def #{fld_sym}=(value)
  intercept_write(#{find_fld_src}, value){
    #{_fld_writer_code(fld, 'value')}
  }
end
RUBY
          cls.send :alias_method, "#{fld_sym}?".to_sym, fld_sym if fld.type.isBool?
          self.send :include, cls
        end

        def start() _define_meta() end
        def finish() end

        #------------------------------------------------------------------------
        # Returns a string representation of this +Sig+ conforming to
        # the Alloy syntax
        #------------------------------------------------------------------------
        def to_alloy
          psig = superclass
          psig_str = (psig != Sig.class) ? "extends #{psig.relative_name} " : ""
          <<-EOS
sig #{relative_name} #{psig_str} {
#{meta.fields_to_alloy}

// inv fields (synthesized)
/*
#{meta.inv_fields_to_alloy}
*/
}
EOS
        end

        protected

        def _fld_reader_code(fld) "@#{fld.getter_sym}" end
        def _fld_writer_code(fld, val) "@#{fld.getter_sym} = #{val}" end

        def _traverse_fields(hash, cont, &block)
          hash.each { |k,v| cont.call(k, v) }
          unless block.nil?
            ret = block.call
            ret.each { |k,v| cont.call(k, v) }
          end
          nil
        end

        def _traverse_field_args(args, cont)
          case
          when args.size == 3
            cont.call(*args)
          when args.size == 2
            if Hash === args[0] && args[0].size == 1
              cont.call(*args[0].first, args[1])
            else
              cont.call(*args)
            end
          when args.size == 1 && Hash === args[0]
            name, type = args[0].first
            cont.call(name, type, Hash[args[0].drop 1])
          else
            msg = """
Invalid field format. Valid formats:
  - field name, type, options_hash={}
  - field name_type_hash, options_hash={}; where name_type_hash.size == 1
  - field hash                           ; where name,type = hash.first
                                           options_hash = Hash[hash.drop 1]
"""
            raise ArgumentError, msg
          end
        end

        def _set_abstract
          meta.set_abstract
        end

        def _set_placeholder
          _set_abstract
          meta.set_placeholder
        end

        # -----------------------------------------------------------------------
        # This is called not during class definition.
        # -----------------------------------------------------------------------
        def _add_inv_for_field(f)
          inv_fld = meta.add_inv_field_for(f)
          fld_accessors inv_fld
          inv_fld
        end

        #------------------------------------------------------------------------
        # Defines the +meta+ method which returns some meta info
        # about this sig's fields
        #------------------------------------------------------------------------
        def _define_meta()
          meta = Alloy::Ast::SigMeta.new(self)
          define_singleton_method(:meta, lambda {meta})
        end

        #------------------------------------------------------------------------
        # Checks whether the specified hash contains exactly one
        # entry, whose key is a valid identifier, and whose value is a
        # subtype of the specified type (`expected_type')
        # ------------------------------------------------------------------------
        def _check_single_fld_hash(hash, expected_type)
          msg1 = "Hash expected, got #{hash.class} instead"
          msg2 = "Expected exactly one entry, got #{hash.length}"
          raise ArgumentError, msg1 unless hash.kind_of? Hash
          raise ArgumentError, msg2 unless hash.length == 1

          varname, type = hash.first
          msg = "`#{varname}' is not a proper identifier"
          raise ArgumentError, msg unless SDGUtils::MetaUtils.check_identifier(varname)
          Alloy::Ast::TypeChecker.check_type(expected_type, type)
        end
      end
    end

    #------------------------------------------
    # == Module ASig
    #------------------------------------------
    module ASig
      def self.included(base)
        base.extend(Static)
        base.extend(Alloy::Dsl::StaticHelpers)
        base.send :include, Alloy::Dsl::InstanceHelpers
        base.start
      end

      def meta
        self.class.meta
      end

      def initialize(*args)
        super
        init_default_transient_values
      end

      def read_field(fld)
        send(Alloy::Ast::FieldMeta.getter_sym(fld))
      end

      def write_field(fld, val)
        send(Alloy::Ast::FieldMeta.setter_sym(fld), val)
      end

      protected

      include Alloy::EventConstants

      def intercept_read(fld)
        _fld_pre_read(fld)
        value = yield
        _fld_post_read(fld, value)
        value
      end

      def intercept_write(fld, value)
        _fld_pre_write(fld, value)
        yield
        _fld_post_write(fld, value)
      end

      def _fld_pre_read(fld)
        Alloy.boss.fire E_FIELD_TRY_READ, :object => self, :field => fld
        _check_fld_read_access(fld)
      end

      def _fld_pre_write(fld, val)
        Alloy.boss.fire E_FIELD_TRY_WRITE, :object => self, :field => fld, :value => val
        _check_fld_write_access(fld, val)
      end

      def _fld_post_read(fld, val)
        Alloy.boss.fire E_FIELD_READ, :object => self, :field => fld, :return => val
      end

      def _fld_post_write(fld, val)
        Alloy.boss.fire E_FIELD_WRITTEN, :object => self, :field => fld, :value => val
      end

      def init_default_transient_values
        meta.tfields.each do |tf|
          if tf.type.unary? && tf.type.range.cls.primitive?
            val = tf.type.range.cls.default_value
            self.write_field(tf, val)
          end
        end
      end

      # checks field read access and raises an error if a violation is detected
      def _check_fld_read_access(fld)
        #TODO
        true
      end

      # checks field write access and raises an error if a violation is detected
      def _check_fld_write_access(fld, value)
        #TODO
        true
      end

    end

    #------------------------------------------
    # == Class Sig
    #------------------------------------------
    class Sig
      include ASig
      placeholder
    end

    def self.create_sig(name, super_cls=Alloy::Ast::Sig)
      cls = Class.new(super_cls)
      SDGUtils::MetaUtils.assign_const(name, cls)
      cls.created if cls.respond_to? :created
      cls
    end

    #------------------------------------------
    # == Module AType
    #------------------------------------------
    module AType
      include Enumerable

      @@DEFAULT_MULT = :lone

      def self.get(obj)
        case obj
        when Proc; DependentType.new(obj)
        else
          UnaryType.new(obj)
        end
      end

      def instantiated?() true end

      def arity
        fail "must override"
      end

      def unary?() arity == 1 end
      def binary?() arity == 2 end
      def ternary?() arity == 3 end

      def primitive?() false end
      def isInt?()    false end
      def isFloat?()  false end
      def isString?() false end
      def isText?()   false end
      def isDate?()   false end
      def isTime?()   false end
      def isBool?()   false end
      def isBlob?()   false end
      def isFile?()   false end

      # @return [Symbol]
      def multiplicity
        @@DEFAULT_MULT
      end

      def remove_multiplicity
        self
      end

      def scalar?
        case multiplicity
        when :one, :lone
          true
        else
          false
        end
      end

      def seq?;  multiplicity == :seq end
      def set?;  multiplicity == :set end
      def one?;  multiplicity == :one end
      def lone?; multiplicity == :lone end

      # Returns a +UnaryType+ at the given position.
      #
      # @param idx [Integer] - position, must be in [0..arity)
      # @return [UnaryType]
      def column(idx)
        raise ArgumentError, "index out of scope, idx=#{idx}, arity=#{arity}" \
          if idx < 0 || idx >= arity
        column!(idx)
      end

      def domain; column!(0) end
      def range; column!(arity - 1) end

      def full_range
        drop(1).reduce(nil) do |acc, utype|
          acc ? ProductType.new(acc, utype) : utype
        end
      end

      def inv
        reduce(nil) do |acc, utype|
          acc ? ProductType.new(utype, acc) : utype
        end
      end

      def each
        for idx in 0..arity-1
           yield column!(idx)
        end
      end

      def *(rhs)
        case rhs
        when AType
          ProductType.new(self, rhs)
        when Class
          ProductType.new(self, UnaryType.new(rhs))
        when Symbol
          ProductType.new(self, UnaryType.new(rhs))
        else
          raise NoMethodError, "undefined multiplication of AType and #{rhs.class.name}"
        end
      end

      def column!(idx)
        fail "must override"
      end

      def to_alloy
        case self
        when UnaryType
          self.cls.to_s.relative_name
        when ProductType
          if self.rhs.arity > 1
            "#{lhs.to_alloy} -> (#{rhs.to_alloy})"
          else
            "#{lhs.to_alloy} -> #{rhs.to_alloy}"
          end
        when ModType
          if @type.arity > 1
            "#{@mult} (#{@type.to_alloy})"
          else
            "#{@mult} #{@type.to_alloy}"
          end
        end
      end
    end

    class DependentType
      include SDGUtils::Delegate
      include AType

      def initialize(proc, inst=nil)
        @proc = proc
        @inst = inst
        if inst
          delegate :arity, :column!, :to => lambda{@proc.call(inst)}
        else
          class << self
            def arity()      0 end
            def column!(idx) fail "Dependent type not instantiated" end
          end
        end
      end

      def instantiate(inst)
        DependentType.new(@type, inst)
      end

      def instantiated?() !@inst.nil? end
      def my_proc() @proc end
      def my_inst() @inst end
    end

    #------------------------------------------
    # == Class UnaryType
    #
    # @attr_reader cls [ColType]
    #------------------------------------------
    class UnaryType
      include AType

      #TODO: rename to something more sensical
      attr_reader :cls

      #----------------------------------------------------------
      # == Class +ColType+
      #
      # @attr_reader src [Object]  - whatever source was used to
      #                              create this this +ColType+
      # @attr_reader klass [Class] - corresponding +Class+
      #----------------------------------------------------------
      class ColType
        attr_reader :src, :klass

        def initialize(src)
          @src = src
          @klass = nil
        end

        def self.inherited(subclass)
          subclass.instance_eval do
            def initialize(src)
              super
            end
          end
        end

        class PrimitiveColType < ColType
        end

        def self.prim(kls, def_val)
          cls = Class.new(PrimitiveColType)
          cls.send(:define_singleton_method, :klass, lambda{kls})
          cls.send(:define_method, :klass, lambda{kls})
          cls.send(:define_method, :default_value, lambda{def_val})
          cls
        end

        class IntColType           < prim(Integer, 0); end
        class FloatColType         < prim(Float, 0.0); end
        class StringColType        < prim(String, ""); end
        class TextColType          < prim(String, ""); end
        class BoolColType          < prim(Integer, false); end
        class DateColType          < prim(Date, nil); end
        class TimeColType          < prim(Time, nil); end
        class BlobColType          < prim(Array, nil); end
        class RefColType           < ColType
          def klass; src end
        end
        class UnresolvedRefColType < ColType
          attr_reader :mod
          def initialize(src, mod)
            super(src)
            @mod = mod
            @klass = nil
          end
          def klass
            msg  = "`klass' method not available for #{self}:#{self.class}.\n"
            msg += "Did you forget run Red::Initializer.resolve_fields?"
            fail msg
          end
        end

        @@built_in_types = {
          :Int     => IntColType.new(:Int),
          :Integer => IntColType.new(:Integer),
          :Float   => FloatColType.new(:Float),
          :String  => StringColType.new(:String),
          :Text    => TextColType.new(:Text),
          :Bool    => BoolColType.new(:Bool),
          :Boolean => BoolColType.new(:Boolean),
          :Date    => DateColType.new(:Date),
          :Time    => TimeColType.new(:Time),
          :Blob    => BlobColType.new(:Blob),
        }

        def self.get(sym)
          case sym
          when NilClass
            raise TypeError, "nil is not a valid type"
          when ColType
            sym
          when Class
            if sym == Integer
              IntColType.new(sym)
            elsif sym == Float
              FloatColType.new(sym)
            elsif sym == String
              StringColType.new(sym)
            elsif sym == Date
              DateColType.new(sym)
            elsif sym == Time
              TimeColType.new(sym)
            else
              RefColType.new(sym)
            end
          when String
            self.get(sym.to_sym)
          when Symbol
            builtin = @@built_in_types[sym]
            mgr = Alloy::DslEngine::ModelBuilder.get
            builtin ||= UnresolvedRefColType.new(sym, mgr.scope_module)
          else
            raise TypeError, "`#{sym}' must be Class or Symbol or String, instead it is #{sym.class}"
          end
        end

        def primitive?
          kind_of? PrimitiveColType
        end

        # Returns string representing corresponding database type
        # supported by +ActiveRecord+.
        def to_db_s
          case self
          when IntColType; "integer"
          when FloatColType; "float"
          when StringColType; "string"
          when TextColType; "text"
          when DateColType; "date"
          when TimeColType; "time"
          when BoolColType; "boolean"
          when BlobColType; "binary"
          else
            @src.to_s.relative_name
          end
        end

        def to_ember_s
          case self
          when IntColType, FloatColType; "number"
          when StringColType, TextColType; "string"
          when DateColType, TimeColType; "date"
          when BoolColType; "boolean"
          else
            #TODO fail?
            "string"
          end
        end

        def from_str(str)
          case self
          when IntColType; Integer(str)
          when FloatColType; Float(str)
          when StringColType; str
          when TextColType; str
          when DateColType; nil #TODO
          when TimeColType; nil #TODO
          when BoolColType; str == "true" ? true : (str == "false" ? false : nil)
          when BlobColType; nil #TODO
          else
            nil
          end
        end

        # Returns the database type converted to +Symbol+.
        def to_db_sym
          to_db_s.to_sym
        end

        def to_s
          case self
          when IntColType; "Int"
          when StringColType; "String"
          when TextColType; "Text"
          when DateColType; "Date"
          else
            @src.to_s #TODO
          end
        end
      end

      def initialize(cls)
        @cls = ColType.get(cls)
        unless @cls.instance_of? ColType::UnresolvedRefColType
          freeze
        end
      end

      # Allowed to call this method only once, only to
      # update an unresolved type
      def update_cls(cls)
        @cls = ColType.get(cls)
        freeze
      end

      def klass()      @cls.klass end
      def arity()      1 end
      def column!(idx) self end

      def primitive?() @cls.primitive? end
      def isInt?()     scalar? && ColType::IntColType === @cls end
      def isFloat?()   scalar? && ColType::FloatColType === @cls end
      def isString?()  scalar? && ColType::StringColType === @cls end
      def isText?()    scalar? && ColType::TextColType === @cls end
      def isDate?()    scalar? && ColType::DateColType === @cls end
      def isTime?()    scalar? && ColType::TimeColType === @cls end
      def isBool?()    scalar? && ColType::BoolColType === @cls end
      def isBlob?()    scalar? && ColType::BlobColType === @cls end
      def isFile?()    scalar? && (klass.isFile?() rescue false) end

      def to_s
        @cls.to_s
      end
    end

    #------------------------------------------
    # == Class ProductType
    #------------------------------------------
    class ProductType
      include AType

      attr_reader :lhs, :rhs

      # @param lhs [AType]
      # @param rhs [AType]
      def initialize(lhs, rhs)
        check_sub(lhs)
        check_sub(rhs)
        @lhs = lhs
        @rhs = rhs
        freeze
      end

      def arity
        lhs.arity + rhs.arity
      end

      def column!(idx)
        if idx < lhs.arity
          lhs.column!(idx)
        else
          rhs.column!(idx-lhs.arity)
        end
      end

      def to_s
        if rhs.arity > 1
          "#{lhs.to_s} -> (#{rhs.to_s})"
        else
          "#{lhs.to_s} -> #{rhs.to_s}"
        end
      end

      private

      def check_sub(x)
        raise ArgumentError, "AType expected, got #{x.class}" \
          unless x.kind_of?(AType)
      end
    end

    #-----------------------------------------------------
    # == Class ModType
    #
    # Wraps another type and adds a multiplicity modifier
    #-----------------------------------------------------
    class ModType
      include AType

      attr_reader :mult, :type

      # @param type [AType]
      # @param mult [Symbol]
      def initialize(type, mult)
        @type = type
        @mult = mult
        freeze
      end

      def arity
        @type.arity
      end

      def column!(idx)
        @type.column!(idx)
      end

      def multiplicity
        @mult
      end

      def remove_multiplicity
        @type
      end

      def to_s
        if @type.arity > 1
          "#{@mult} (#{@type.to_s})"
        else
          "#{@mult} #{@type.to_s}"
        end
      end
    end

    #-----------------------------------------------------
    # == Class +TypeChecker+
    #-----------------------------------------------------
    class TypeChecker
      def self.check_type(expected, actual)
        #TODO
      end
    end

    #-----------------------------------------------------
    # == Class +Utils+
    #-----------------------------------------------------
    class Utils
      class << self
      end
    end

  end
end
