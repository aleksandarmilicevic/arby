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

      def check(scope, given_name=nil, &body)
        __command(:check, scope, given_name, &body)
      end

      # def run(scope, given_name=nil, &body)
      #   __command(:run, scope, given_name, &body)
      # end

      private

      def __command(kind, scope, given_name=nil, &body)
        name = given_name || "#{kind}_#{meta.checks.size}"
        pred = _create_fn(:pred, name, {}, nil, &body)
        _define_method_for_fun(pred)
        cmd = Alloy::Ast::Command.new(kind, given_name, scope, pred)
        meta.add_command cmd
        cmd
      end

    end

  end
end
