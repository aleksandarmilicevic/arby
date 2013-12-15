require 'arby/bridge/compiler'
require 'arby/bridge/solution'

module Arby
  module Bridge
    module SolverHelpers

      def find_instance(scope="")
        run_cmd_name = "find_model_#{SDGUtils::Random.salted_timestamp}"
        run_cmd = "run #{run_cmd_name} {} #{scope}"
        als_model = "#{to_als}\n\n#{run_cmd}"

        comp = Arby::Bridge::Compiler.compile(als_model)
        sol = comp.execute_command(run_cmd_name)
        if sol.satisfiable?
          sol.arby_instance
        else
          nil
        end
      end

    end
  end
end
