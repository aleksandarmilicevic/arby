require 'alloy/alloy_event_constants.rb'
require 'alloy/ast/field_meta'
require 'alloy/ast/sig_meta'
require 'alloy/utils/codegen_repo'
require 'sdg_utils/meta_utils'

module Alloy
  module Ast

    #=========================================================================
    # == Module ASig::Static
    #=========================================================================
    module ASig
      module Static
        def inherited(subclass)
          super
          fail "The +meta+ method hasn't been defined for class #{self}" unless meta
          subclass.start
          meta.add_subsig(subclass)
        end

        def created()
          require 'alloy/alloy.rb'
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
        # Defines fields inside the class definition
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

  end
end
