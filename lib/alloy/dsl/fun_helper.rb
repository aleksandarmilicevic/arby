require 'alloy/ast/fun'
require 'alloy/ast/arg'
require 'alloy/ast/types'
require 'alloy/dsl/fields_helper'
require 'alloy/dsl/errors'
require 'alloy/utils/codegen_repo'
require 'sdg_utils/dsl/base_builder'
require 'sdg_utils/lambda/sourcerer'

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
        return unless Alloy.conf.turn_methods_into_funs
        return unless SDGUtils::DSL::BaseBuilder.in_body?
        meth = self.instance_method(name)
        fun_args = meth.parameters.map{ |mod, sym|
          Alloy::Ast::Arg.new :name => sym, :type => Alloy::Ast::NoType.new
        }
        fun = Alloy::Ast::Fun.fun :name     => name,
                                  :args     => fun_args,
                                  :ret_type => Alloy::Ast::NoType.new,
                                  :parent   => self,
                                  :body     => meth.bind(allocate).to_proc
        meta.add_fun fun
      end

      private

      def _create_and_add_fn(kind, *args, &block)
        _catch_syntax_errors do
          fun_opts = _to_fun_opts(*args, &block)
          fn = Alloy::Ast::Fun.send kind, fun_opts
          meta.send :"add_#{kind}", fn
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
        rescue => ex
          raise SyntaxError.new(ex)
        end
      end

      # if block is provided,
      #   args must contain a single symbol
      # else
      #   args should match to the +class_eval+ formal parameters
      def _define_method(*args, &block)
        _catch_syntax_errors do
          old = [Alloy.conf.turn_methods_into_funs,
                 Alloy.conf.allow_undef_vars,
                 Alloy.conf.allow_undef_consts]
          Alloy.conf.turn_methods_into_funs,
          Alloy.conf.allow_undef_vars,
          Alloy.conf.allow_undef_consts = false, false, false
          begin
            if block.nil?
              Alloy::Utils::CodegenRepo.eval_code self, *args, :kind => :user_block
            else
              define_method args[0], &block
            end
          rescue ::SyntaxError => ex
            src = block ? block.source : args[0]
            msg = "syntax error in:\n  #{src}"
            raise SyntaxError.new(ex), msg
          ensure
            Alloy.conf.turn_methods_into_funs,
            Alloy.conf.allow_undef_vars,
            Alloy.conf.allow_undef_consts = old
          end
        end
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
            _define_method <<-RUBY, __FILE__, __LINE__+1
              def #{fun.name}(#{args_str})
              end
            RUBY
          else
            proc_src_loc = proc.source_location rescue nil
            if proc_src_loc &&
                proc_src = (SDGUtils::Lambda::Sourcerer.proc_to_src(proc) rescue nil)
              _define_method <<-RUBY, *proc_src_loc
                def #{fun.name}(#{args_str})
                  #{proc_src}
                end
              RUBY
            else
              fail "unimplemented"
            end
          end
        end
      end

      # def _define_method_for_fun(fun)
      #   _catch_syntax_errors do
      #     proc = fun.body || proc{}
      #     method_body_name = "#{fun.name}_body__#{SDGUtils::Random.salted_timestamp}"
      #     _define_method method_body_name.to_sym, &proc

      #     if fun.arity == proc.arity
      #       _define_method fun.name.to_sym, &proc
      #     else
      #       msg = "number of function (#{fun.name}) formal parameters (#{fun.arity})"+
      #             " doesn't match the arity of the given block (#{proc.arity})"
      #       raise ArgumentError, msg unless proc.arity == 0
      #       args_str = fun.args.map(&:name).join(", ")
      #       arg_map_str = fun.args.map{|a| "#{a.name}: #{a.name}"}.join(", ")
      #       _define_method <<-RUBY, __FILE__, __LINE__+1
      #         def #{fun.name}(#{args_str})
      #           shadow_methods_while({#{arg_map_str}}) do
      #             #{method_body_name}
      #           end
      #         end
      #       RUBY
      #     end
      #   end
      # end

      def _to_args(hash)
        ans = []
        _traverse_fields_hash hash, lambda {|arg_name, type|
          arg = Alloy::Ast::Arg.new :name => arg_name, :type => type
          ans << arg
        }
        ans
      end

      def _to_fun_opts(*args, &block)
        fun_opts =
          case
          when args.size == 1 && Hash === args[0]
            fa = _to_args(args[0][:args])
            args[0].merge :args => fa
          when args.size == 1 && Alloy::Ast::Fun === args[0]
            args[0]
          when args.size == 1 && FunBuilder === args[0]
            fb = args[0]
            { :name     => fb.name,
              :args     => _to_args(fb.args),
              :ret_type => fb.ret_type,
              :body     => fb.body}
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
            raise ArgumentError, """
Invalid fun format. Valid formats:
  - fun(opts [Hash])
  - fun(fun [Fun])
  - fun(name [String], full_type [Hash])
  - fun(name [String], args [Hash], ret_type [AType])
"""
          end
        msg = "two blocks provided (both in args and explicitly)"
        raise ArgumentError, msg if block && fun_opts[:body]
        block = fun_opts[:body] || block || proc{}
        fun_opts.merge!({:body => block, :parent => self})
      end

    end

  end
end
