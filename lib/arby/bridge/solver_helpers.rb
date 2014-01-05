require 'arby/bridge/compiler'

module Arby
  module Bridge
    module SolverHelpers

      def solve(pred=nil, scope="", bounds=nil)
        require 'arby/bridge/compiler'
        require 'arby/bridge/solution'

        cmd_name, cmd_body = if pred
                               [pred, ""]
                             else
                               ["find_model_#{SDGUtils::Random.salted_timestamp}", "{}"]
                             end
        run_cmd = "run #{cmd_name} #{cmd_body} #{scope}"
        als_model = "#{to_als}\n\n#{run_cmd}"

        # puts "Solving this"
        # puts "---"
        # puts als_model
        # puts "---"
        comp = Arby::Bridge::Compiler.compile(als_model)
        comp.execute_command(cmd_name, bounds)
      end

      def execute_command(cmd_idx_or_name=0, bounds=nil)
        comp = Arby::Bridge::Compiler.compile(to_als)
        comp.execute_command(cmd_idx_or_name, bounds)
      end

      def find_instance(pred=nil, scope="", bounds=nil)
        sol = solve(pred, scope, bounds)
        if sol.satisfiable?
          sol.arby_instance
        else
          nil
        end
      end

    end
  end
end
