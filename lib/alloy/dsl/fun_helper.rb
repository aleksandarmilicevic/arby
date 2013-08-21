require 'alloy/ast/fun'
require 'alloy/ast/arg'
require 'alloy/ast/types'
require 'alloy/dsl/fields_helper'
require 'alloy/dsl/fun_instrumenter'
require 'alloy/dsl/errors'
require 'alloy/utils/codegen_repo'
require 'sdg_utils/dsl/base_builder'

module Alloy
  module Dsl

    module FunHelper
      include FieldsHelper

      # ---------------------------------------------------------
      # TODO: DOCS
      # ---------------------------------------------------------

      def pred(*args, &block)
        _create_and_add_fn(:pred, *args, &block)
      end

      def fun(*args, &block)
        _create_and_add_fn(:fun, *args, &block)
      end

      def fact(*args, &block)
        _create_and_add_fn(:fact, *args, &block)
      end

      def assertion(*args, &block)
        _create_and_add_fn(:assertion, *args, &block)
      end

      def invariant(&block)
        _define_method(:invariant, &block)
      end

      def method_missing(sym, *args, &block)
        return super if Alloy.is_caller_from_alloy?(caller[0])
        begin
          super
        rescue => ex
          # use this as a last resort
          raise ex unless Alloy.conf.allow_undef_vars
          raise ex unless SDGUtils::DSL::BaseBuilder.in_body?
          raise ex unless args.empty?
          FunBuilder.new(sym, &block)
        end
      end

      def method_added(name)
        return if Alloy.is_caller_from_alloy?(caller[0])
        return unless Alloy.conf.turn_methods_into_funs
        return unless SDGUtils::DSL::BaseBuilder.in_body?

        meth = self.instance_method(name)
        fun_args = _args_from_proc(meth)
        dummy_target =
          if Class === self
            self.allocate
          else # it must be a Module
            obj = Object.new
            obj.singleton_class.send :include, self
            obj
          end
        fun_body = meth.bind(dummy_target).to_proc
        fun = Alloy::Ast::Fun.fun :name     => name,
                                  :args     => fun_args,
                                  :ret_type => Alloy::Ast::NoType.new,
                                  :parent   => self,
                                  :body     => fun_body
        meta.add_fun fun
      end

      private

      def _create_and_add_fn(kind, *args, &block)
        _catch_syntax_errors do
          fun_opts = _to_fun_opts(*args, &block)
          fn = Alloy::Ast::Fun.send kind, fun_opts
          meta.send "add_#{kind}".to_sym, fn
          _define_method_for_fun(fn)
          fn
        end
      end

      def _create_fn(kind, *args, &block)
        _catch_syntax_errors do
          fun_opts = _to_fun_opts(*args, &block)
          Alloy::Ast::Fun.send kind, fun_opts
        end
      end

      def _catch_syntax_errors
        begin
          yield
        rescue Alloy::Dsl::SyntaxError => ex
          raise
        rescue Exception => ex
          raise Alloy::Dsl::SyntaxError.new(ex)
        end
      end

      # if block is provided,
      #   args must contain a single symbol
      # else
      #   args should match to the +class_eval+ formal parameters
      def _define_method(*args, &block)
        old = Alloy.conf.turn_methods_into_funs
        Alloy.conf.turn_methods_into_funs = false
        name, file, line = *args
        _catch_syntax_errors do
          begin
            if block.nil?
              desc = {:kind => :user_block}
              Alloy::Utils::CodegenRepo.eval_code self, name, file, line, desc
            else
              define_method name, &block
            end
          rescue ::SyntaxError => ex
            src = block ? block.source : name
            msg = "syntax error in:\n  #{src}"
            raise SyntaxError.new(ex), msg
          end
        end
      ensure
        Alloy.conf.turn_methods_into_funs = old
      end

      def _define_method_for_fun(fun)
        _catch_syntax_errors do
          proc = fun.body || proc{}

          if fun.arity != proc.arity && proc.arity != 0
            msg = "number of function `#{fun.name}' formal parameters (#{fun.arity})" +
                  " doesn't match the arity of the given block (#{proc.arity})"
            raise ArgumentError, msg
          end

          args_str = fun.args.map(&:name).join(", ")
          if fun.body.nil?
            _define_method "def #{fun.name}(#{args_str}) end", __FILE__, __LINE__
          else
            proc_src_loc = proc.source_location rescue nil
            orig_src, instr_src = FunInstrumenter.new(proc).instrument # rescue []
            if proc_src_loc && orig_src
              _define_method <<-RUBY, *proc_src_loc
  def #{fun.name}(#{args_str})
    #{orig_src}
  end
RUBY
              _define_method <<-RUBY
  def #{fun.name}_alloy(#{args_str})
    #{instr_src}
  end
RUBY
            else
              #TODO: doesn't work for module methods (because of some scoping issues)
              method_body_name = "#{fun.name}_body__#{SDGUtils::Random.salted_timestamp}"
              _define_method method_body_name.to_sym, &proc
              if fun.arity == proc.arity
                _define_method fun.name.to_sym, &proc
              else
                arg_map_str = fun.args.map{|a| "#{a.name}: #{a.name}"}.join(", ")
                _define_method <<-RUBY
                  def #{fun.name}(#{args_str})
                    shadow_methods_while({#{arg_map_str}}) do
                      #{method_body_name}
                    end
                  end
                RUBY
              end
            end
          end
        end
      end

      def _to_args(hash)
        ans = []
        _traverse_fields_hash hash, lambda {|arg_name, type|
          arg = Alloy::Ast::Arg.new :name => arg_name, :type => type
          ans << arg
        }
        ans
      end

      def _args_from_proc(proc)
        return [] unless proc
        proc.parameters.map{ |mod, sym|
          Alloy::Ast::Arg.new :name => sym, :type => Alloy::Ast::NoType.new
        }
      end

      def _to_fun_opts(*args, &block)
        fun_opts =
          case
          when args.size == 1
            case a = args[0]
            when Hash
              hash = a
              fa = _to_args(hash[:args])
              hash.merge :args => fa
            when Alloy::Ast::Fun
              a
            when FunBuilder
              fb = args[0]
              { :name     => fb.name,
                :args     => _to_args(fb.args),
                :ret_type => fb.ret_type,
                :body     => fb.body }
            when String, Symbol
              { :name     => a.to_s,
                :args     => _args_from_proc(block),
                :ret_type => Alloy::Ast::NoType.new }
            else
              binding.pry
              _raise_invalid_format("invalid single arg type: #{a.class}")
            end
          when args.size == 2
            # expected types: String, Hash
            fun_name = args[0]
            fun_args = _to_args(args[1])
            { :name     => fun_name,
              :args     => fun_args[0...-1],
              :ret_type => fun_args[-1].type }
          when args.size == 3
            # expected types: String, Hash, AType
            { :name     => args[0],
              :args     => _to_args(args[1]),
              :ret_type => args[2] }
          else
            _raise_invalid_format
          end
        msg = "two blocks provided (both in args and explicitly)"
        raise ArgumentError, msg if block && fun_opts[:body]
        block = fun_opts[:body] || block || proc{}
        fun_opts.merge!({:body => block, :parent => self})
      end

      def _raise_invalid_format(str="")
        raise ArgumentError, """Invalid fun format: #{str}
Valid formats:
  - fun(opts [Hash])
  - fun(fun [Fun])
  - fun(name [String], full_type [Hash])
  - fun(name [String], args [Hash], ret_type [AType])
"""
      end

    end

  end
end
