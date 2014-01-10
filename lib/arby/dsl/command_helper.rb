require 'arby/ast/command'
require 'arby/ast/fun'
require 'arby/ast/scope'
require 'arby/dsl/errors'

module Arby
  module Dsl

    # REQUIREMENTS
    #   FunHelper included
    #   meta.checks
    #   meta.add_check
    #   meta.runs
    #   meta.add_run
    module CommandHelper
      def check(*name_and_scope, &body)
        __command(:check, *name_and_scope, &body)
      end

      def run(*name_and_scope, &body)
        if caller[0].end_with?("block in _run_suite'")
          super
        else
          __command(:run, *name_and_scope, &body)
        end
      end

      private

      def __command(kind, *name_scope_exceptions, &body)
        msg = "Too many commmand args: expected max 3, got #{name_scope_exceptions}"
        raise SyntaxError, msg if name_scope_exceptions.size > 3
        msg = "Too few command args: at least <scope> expected, got nothing"
        fail SyntaxError, msg if name_scope_exceptions.empty?

        scope, name = []
        exceptions = {}
        name_scope_exceptions.each do |x|
          case x
          when String, Symbol then !name ? name = x : scope = x.gsub(/^for /, "")
          when Integer        then scope = x
          when Hash           then exceptions = x
          else
            raise SyntaxError, "Unexpected argument type: " +
              "expected String, Integer, or Hash, got #{x}:#{x.class}"
          end
        end
        __cmd(kind, name, scope, exceptions, &body)
      end

      def __cmd(kind, name=nil, scope=nil, exceptions=nil, &body)
        pred_name = name || "#{kind}_#{meta.checks.size}"
        pred = nil
        if body
          pred = _create_fn(:pred, pred_name, {}, nil, &body)
          _define_method_for_fun(pred)
        end

        sig_scopes = CommandHelper.__parse_sig_scope_hash(exceptions)
        scope = Arby::Ast::Scope.new(scope, sig_scopes)

        cmd = Arby::Ast::Command.new(kind, name, scope, pred)
        meta.add_command cmd
        cmd
      end

      def self.__parse_sig_scope_hash(hash={})
        hash.map do |sig_spec, scope|
          sig = case sig_spec
                when String, Symbol then sig = Arby.meta.find_sig(sig_spec)
                when Class          then sig = sig_spec if sig_spec < Arby::Ast::ASig
                end
          sig or raise SyntaxError, "Invalid sig #{sig_spec}:#{sig_spec.class}"

          case scope
          when Arby::Ast::SigScope
            Arby::Ast::SigScope.new(sig || scope.sig, scope.scope, scope.exact?)
          when Integer
            Arby::Ast::SigScope.new(sig, scope)
          else
            raise SyntaxError, "Invalid scope #{scope}:#{scope.class}"
          end
        end
      end
    end

  end
end
