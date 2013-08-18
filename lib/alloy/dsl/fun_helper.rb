require 'alloy/ast/fun'
require 'alloy/ast/arg'
require 'alloy/ast/types'
require 'alloy/dsl/errors'

module Alloy
  module Dsl

    module FunHelper
      # ---------------------------------------------------------
      # TODO: DOCS
      # ---------------------------------------------------------

      def pred(*args, &block)
        pred = _create_pred(*args, &block)
        meta.add_pred(pred)
        _define_method_for_fun(pred)
      end

      def fun(*args, &block)
        fun = _create_fun(*args, &block)
        meta.add_fun(fun)
        _define_method_for_fun(fun)
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
          raise ex unless SigBuilder.in_sig_body?
          raise ex unless args.empty? && block.nil?
          FunBuilder.new(sym)
        end
      end

      def method_added(name)
        return unless Alloy.conf.turn_methods_into_funs
        return unless SigBuilder.in_sig_body?
        meth = self.instance_method(name)
        fun_args = meth.parameters.map{ |mod, sym|
          Alloy::Ast::Arg.new :name => sym, :type => Alloy::Ast::NoType.new
        }
        fun = Alloy::Ast::Fun.new :name     => name,
                                  :args     => fun_args,
                                  :ret_type => Alloy::Ast::NoType.new,
                                  :parent   => self,
                                  :body     => meth.bind(allocate).to_proc
        meta.add_fun fun
      end

      private

      def _create_fun(*args, &block)  _create_f(:fun, *args, &block) end
      def _create_pred(*args, &block) _create_f(:pred, *args, &block) end

      def _create_f(kind, *args, &block)
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
              class_eval *args
            else
              define_method(args[0], &block)
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
          method_body_name = "#{fun.name}_body__#{SDGUtils::Random.salted_timestamp}"
          _define_method method_body_name.to_sym, &proc

          if fun.arity == proc.arity
            _define_method fun.name.to_sym, &proc
          else
            msg = "number of function (#{fun.name}) formal parameters (#{fun.arity}) " +
                  "doesn't match the arity of the given block (#{proc.arity})"
            raise ArgumentError, msg unless proc.arity == 0
            args_str = fun.args.map(&:name).join(", ")
            arg_map_str = fun.args.map{|a| "#{a.name}: #{a.name}"}.join(", ")
            _define_method <<-RUBY, __FILE__, __LINE__+1
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
end
