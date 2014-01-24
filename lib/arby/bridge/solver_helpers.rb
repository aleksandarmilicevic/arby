module Arby
  module Bridge
    module SolverHelpers

      def compile
        require 'arby/bridge/compiler'
        Arby::Bridge::Compiler.compile(self)
      end

      def solve(*pred_scope_bounds, &block)
        require 'arby/bridge/compiler'
        require 'arby/bridge/solution'

        if !block
          pred = pred_scope_bounds[0]
          scope_bounds = pred_scope_bounds[1..-1]
        else
          pred = nil
          scope_bounds = pred_scope_bounds
        end

        grps = scope_bounds.group_by{|e| e.is_a? Arby::Ast::Bounds}
        bounds = Array(grps[true]).first
        scope = Arby::Dsl::CommandHelper.parse_scope(*Array(grps[false]))
        scope.extend_for_bounds(bounds)

        cmd_name, cmd_body = if pred
                               [pred, ""]
                             else
                               ["find_model_#{SDGUtils::Random.salted_timestamp}", "{}"]
                             end
        run_cmd = "run #{cmd_name} #{cmd_body} #{scope.to_als}"
        als_model = "#{to_als}\n\n#{run_cmd}"

        # puts "Solving this"
        # puts "---"
        # puts als_model.inspect
        # puts "---"

        comp = Arby::Bridge::Compiler.compile(self, als_model)
        comp.execute_command(-1, bounds)
      end

      def execute_command(cmd_idx_or_name=0, bounds=nil)
        require 'arby/bridge/compiler'
        comp = Arby::Bridge::Compiler.compile(self)
        comp.execute_command(cmd_idx_or_name, bounds)
      end

      def find_instance(pred=nil, *scope_bounds)
        sol = solve(pred, *scope_bounds)
        if sol.satisfiable?
          sol.arby_instance
        else
          nil
        end
      end

    end
  end
end
