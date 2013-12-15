require 'arby/bridge/compiler'
require 'arby/bridge/solution'

module Arby
  module Bridge
    module SolverHelpers

      def find_instance(pred=nil, scope="")
        cmd_name, cmd_body = if pred
                               [pred, ""]
                             else
                               ["find_model_#{SDGUtils::Random.salted_timestamp}", "{}"]
                             end
        run_cmd = "run #{cmd_name} #{cmd_body} #{scope}"
        als_model = "#{to_als}\n\n#{run_cmd}"

        comp = Arby::Bridge::Compiler.compile(als_model)
        sol = comp.execute_command(cmd_name)
        if sol.satisfiable?
          sol.arby_instance
        else
          nil
        end
      end

    end
  end
end
