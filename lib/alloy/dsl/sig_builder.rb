require 'alloy/dsl/fun_helper'
require 'alloy/dsl/fun_builder'
require 'alloy/ast/arg'
require 'alloy/ast/fun'
require 'sdg_utils/dsl/class_builder'

module Alloy
  module Dsl

    # ============================================================================
    # == Class +DslApi+
    #
    # Used to create sig classes.
    # ============================================================================
    module SigDslApi
      protected
      
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

      def __created()
        require 'alloy/alloy.rb'
        _define_meta() 
        Alloy.meta.sig_created(self)
      end
      def __params(*args)     fields(*args) end
      def __eval_body(&block) self.class_eval &block end
      def __finish() end
            
      # ~~~~~~~~~~~~~~~~~~~~~~~~~~~ private stuff ~~~~~~~~~~~~~~~~~~~~~~~~~~~ #

      private
      
      #------------------------------------------------------------------------
      # For a given field (name, type) creates a getter and a setter
      # (instance) method, and adds it to this sig's +meta+ instance.
      #
      # @param fld_name [String]
      # @param fld_type [AType]
      #------------------------------------------------------------------------
      def _field(name, type, hash={})
        fld = meta.add_field(name, type, hash)
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
      
      def _traverse_fields(hash, cont, &block)
        _traverse_fields_hash(hash, cont)
        unless block.nil?
          ret = block.call
          _traverse_fields_hash(ret, cont)
        end
        nil
      end
      
      def _traverse_fields_hash(hash, cont)
        return unless hash
        hash.each do |k,v| 
          if Array === k
            k.each{|e| cont.call(e, v)}
          else
            cont.call(k, v) 
          end
        end
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
      
      def _to_args(hash)
        ans = []
        _traverse_fields_hash hash, lambda {|arg_name, type|
          arg = Alloy::Ast::Arg.new :name => arg_name, :type => type
          ans << arg
        }
        ans
      end
      
      def _to_fun_opts(*args, &block)
        block = lambda{} unless block
        fun_opts =
          case
          when args.size == 1 && Hash === args[0]
            fa = _to_args(args[0][:args])
            args[0].merge :args => fa
          when args.size == 1 && Alloy::Ast::Fun === args[0]
            args[0]
          when args.size == 1 && FunBuilder === args[0]
            fb = args[0]
            { :name => fb.name,
            :args => _to_args(fb.args),
            :ret_type => fb.ret_type }
          when args.size == 2
            # expected types: String, Hash
            fun_name = args[0]
            fun_args = _to_args(args[1])
            { :name => fun_name,
            :args => fun_args[0...-1],
            :ret_type => fun_args[-1].type }
          when args.size == 3
            # expected types: String, Hash, AType
            { :name => args[0],
            :args => _to_args(args[1]),
            :ret_type => args[2] }
          else
            raise ArgumentError, """
Invalid fun format. Valid formats:
  - fun(opts [Hash])
  - fun(fun [Fun])
  - fun(name [String], full_type [Hash])
  - fun(name [String], args [Hash], ret_type [AType])
"""
          end
        fun_opts.merge!({:body => block, :parent => self})
      end
      
    end


    # ============================================================================
    # == Class +SigBuilder+
    #
    # Used to create sig classes.
    # ============================================================================
    class SigBuilder < SDGUtils::DSL::ClassBuilder
      def self.get() SDGUtils::DSL::ClassBuilder.get end
      def self.in_body?()  curr = self.get and curr.in_body? end
      def self.in_class?() curr = self.get and curr.in_class? end

      def initialize(options={})
        opts = {
          :superclass => Alloy::Ast::Sig
        }
        super(opts.merge!(options))
      end

      def self.sig(*args, &block)
        new.sig(*args, &block)
      end

      # --------------------------------------------------------------
      # Creates a new class, subclass of either +Alloy::Ast::Sig+ or a
      # user supplied super class, creates a constant with a given
      # +name+ in the callers namespace and assigns the created class
      # to it.
      # --------------------------------------------------------------
      def sig(*args, &block)
        build(*args, &block)
      end
    end


  end
end
