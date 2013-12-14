require 'arby/ast/command'
require 'arby/ast/fun'

module Alloy
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

      def __command(kind, *name_and_scope, &body)
        msg = "Too many commmand args: [<name>, <scope>] expected, got #{name_and_scope}"
        fail msg if name_and_scope.size > 2
        msg = "Too few command args: <scope> expected, got nothing"
        fail msg if name_and_scope.empty?

        scope, given_name = name_and_scope.reverse
        name = given_name || "#{kind}_#{meta.checks.size}"
        pred = nil
        if body
          pred = _create_fn(:pred, name, {}, nil, &body)
          _define_method_for_fun(pred)
        end
        cmd = Alloy::Ast::Command.new(kind, given_name, scope, pred)
        meta.add_command cmd
        cmd
      end

    end

  end
end
