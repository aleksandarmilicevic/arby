require 'alloy/ast/command'
require 'alloy/ast/fun'

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

      # def run(scope, given_name=nil, &body)
      #   __command(:run, scope, given_name, &body)
      # end

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
