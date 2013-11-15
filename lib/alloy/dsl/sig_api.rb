require 'alloy/dsl/fields_helper'
require 'alloy/dsl/fun_helper'
require 'alloy/ast/arg'
require 'alloy/ast/fun'
require 'alloy/ast/types'

module Alloy
  module Dsl

    # ============================================================================
    # == Class +DslApi+
    #
    # Used to create sig classes.
    # ============================================================================
    module SigDslApi
      protected

      include FieldsHelper
      include FunHelper

      # ~~~~~~~~~~~~~~~~~~~~~~~~ DSL API ~~~~~~~~~~~~~~~~~~~~~~~~ #

      # ---------------------------------------------------------
      # TODO: DOCS
      # ---------------------------------------------------------
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

      # ---------------------------------------------------------
      # TODO: DOCS
      # ---------------------------------------------------------
      def field(*args)
        _traverse_field_args(args, lambda {|name, type, hash={}|
                               _field(name, type, hash)})
      end

      alias_method :ref, :field

      def synth_field(name, type)
        field(name, type, :synth => true)
      end

      def abstract()    _set_abstract; self end
      def placeholder() _set_placeholder; self end

      # ~~~~~~~~~~~~~~~~~~~~~ callbacks for ClassBuilder ~~~~~~~~~~~~~~~~~~~~~ #
      protected

      def __created()
        _define_meta()
        require 'alloy/alloy.rb'
        Alloy.meta.add_sig(self)
      end
      def __params(*args)     fields(*args) end
      def __eval_body(&block) 
        if Alloy.conf.detect_appended_facts && 
            SDGUtils::Lambda::Sourcerer.is_curly_block(block) #TODO rescue false
          send :fact, &block
        else
          class_eval &block
        end
      end
      def __finish() end

      # ~~~~~~~~~~~~~~~~~~~~~~~~~~~ private stuff ~~~~~~~~~~~~~~~~~~~~~~~~~~~ #
      private

      #------------------------------------------------------------------------
      # For a given field (name, type) creates a getter and a setter
      # (instance) method, and adds it to this sig's +meta+ instance.
      #
      # @param name [String]
      # @param type [AType]
      #------------------------------------------------------------------------
      def _field(name, type, hash={})
        type = Alloy::Ast::AType.get(type)
        opts = hash.merge(type.args)
        fld = meta.add_field(name, type, opts)
        fld_accessors fld
        fld
      end

      def _fld_reader_code(fld) "@#{fld.getter_sym}" end
      def _fld_writer_code(fld, val) "@#{fld.getter_sym} = #{val}" end

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
          intercept_read(#{find_fld_src}) { #{_fld_reader_code(fld)} }
        end
        def #{fld_sym}=(value)
          intercept_write(#{find_fld_src}, value) { #{_fld_writer_code(fld, 'value')} }
        end
        RUBY
        cls.send :alias_method, "#{fld_sym}?".to_sym, fld_sym if fld.type.isBool?
        self.send :include, cls
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
    end

  end
end
