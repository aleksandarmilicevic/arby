require 'arby/bridge/imports'
require 'arby/bridge/reporter'
require 'arby/bridge/solution'
require 'sdg_utils/random'
require 'sdg_utils/timing/timer'

module Arby
  module Bridge

    def self.debug(str)
      puts str if $pera
    end

    class Compiler

      @@current = nil
      def self.current() @@current end
      def self.current=(c) @@current = c end

      # @model     [Arby::Ast::Model]
      # @bounds    [Arby::Ast::Bounds]
      def self.compile(model, bounds=nil)
        compiler = Compiler.new(model, bounds)
        compiler.send :_parse
        compiler
      end

      def self.solve(model, pred, scope, bounds=nil)
        sc = scope.extend_for_bounds(bounds)
        Compiler.new(model, bounds).solve(pred, sc)
      end

      def self.execute_command(model, cmd_idx_or_name=0, bounds=nil)
        Compiler.new(model, bounds).execute_command(cmd_idx_or_name)
      end

      def model()     @model end
      def univ()      @univ end
      def bounds()    @bounds end
      def _a4world()  @a4world end

      def sigs()       @sigs ||= model.reachable_sigs end
      def type2atype() @type2atype ||= {} end
      def type2sig()   @type2sig ||= {} end

      # @see Compiler.all_fields
      def all_fields
        fail_if_not_parsed
        AlloyCompiler.all_fields(@a4world)
      end

      def solve(pred, scope)
        cmd_name, cmd_body =
          case pred
          when NilClass
            ["find_model_#{SDGUtils::Random.salted_timestamp}", "{}"]
          when String, Symbol
            [pred, ""]
          when Arby::Ast::Fun
            _check_pred(pred)
            [pred.name, ""]
          when Arby::Ast::ConstrainedFun
            _check_pred(pred)
            model = @model.extend.meta
            aux_pred_name = "aux_#{pred.name}_#{SDGUtils::Random.salted_timestamp}"
            aux_pred = model.ruby_module.pred :name => aux_pred_name,
                                              :args => pred.args,
                                              :body => pred.block
            name = "#{pred.name}"
            qdecl = pred.fun.args
            call_p_aux = Arby::Ast::Expr::CallExpr.new nil, aux_pred, *qdecl.map(&:to_e)
            call_p = Arby::Ast::Expr::CallExpr.new nil, pred.fun, *qdecl.map(&:to_e)
            qbody = call_p_aux.and(call_p)
            cbody = Arby::Ast::Expr::QuantExpr.exist(qdecl, qbody)
            cmd = Arby::Ast::Command.new :run, name, scope, cbody
            model.add_command cmd
            @model = model
            nil
          when Arby::Ast::CurriedFun
            _check_pred(pred)
            if not pred.args.empty?
              name = "#{pred.name}"
              model = @model.clone
              qdecl = pred.fun.args[pred.args.size..-1]
              qbody = Arby::Ast::Expr::CallExpr.new nil, pred.fun, *(pred.args + qdecl)
              cbody = if qdecl.empty?
                        qbody
                      else
                        Arby::Ast::Expr::QuantExpr.exist(qdecl, qbody)
                      end
              cmd = Arby::Ast::Command.new :run, name, scope, cbody
              model.add_command cmd
              @model = model
              nil
            else
              [pred.name, ""]
            end
          else
            [pred.to_s, ""]
          end

        cmd_als = cmd_name ? "run #{cmd_name} #{cmd_body} #{scope.to_als}" : ""
        sol = _execute(_parse(cmd_als), -1)
        sol.set_solving_params :solve, pred, scope
        sol
      end

      # @see Compiler.execute_command
      # @result [Arby::Bridge::Solution]
      def execute_command(cmd_idx_or_name=0)
        sol = _execute(_parse(), cmd_idx_or_name)
        sol.set_solving_params :execute_command, cmd_idx_or_name
        sol
      end

      def initialize(model, bounds=nil)
        @model     = Arby::Ast::TypeChecker.get_arby_model(model)
        @bounds    = bounds
        @univ      = bounds ? bounds.extract_universe : nil
        @rep       = nil # we don't care to listen to reports
        @timer     = SDGUtils::Timing::Timer.new

        if @model && @univ
          __pi_atoms = @univ.sig_atoms.reject{|a| find_pi_sig_for_atom(a)}
          unless __pi_atoms.empty?
            __namer = Arby.short_alloy_printer_conf.atom_sig_namer
            @model = @model.extend {
              __pi_atoms.each do |a|
                one sig(__namer[a.class.relative_name, a.__alloy_atom_id] < a.class) do
                  set_atom(a.__alloy_atom_id)
                end
              end
            }.meta
          end
        end
      end

      private

      def find_pi_sig_for_atom(atom)
        sigs.find{ |s|
          s.meta.atom? and
          atom.is_a?(s.superclass) and
          s.meta.atom_id == atom.__alloy_atom_id
        }
      end

      def _check_pred(pred)
        fail "cannot solve a non-pred function: #{pred}" unless pred.pred?
      end

      # @see Compiler.execute_command
      # @result [Arby::Bridge::Solution]
      def _execute(a4wrld, cmd_idx_or_name=0)
        pi = @bounds && @bounds.serialize(@univ)

        Compiler.current = self
        a4sol = @timer.time_it("execute_command") {
          AlloyCompiler.execute_command(a4wrld, cmd_idx_or_name, pi)
        }
        Compiler.current = nil

        sol = Solution.new(a4sol, self, @univ, @bounds, @timer.last_time)
        sol.arby_instance if @univ && !@univ.sig_atoms.empty?
        sol
      end


      # @see Compiler.parse
      def _parse(addendum="")
        # fail "already parsed" if @a4world
        fail "als model not set" unless @model
        als = @model.to_als + "\n" + addendum

        Bridge::debug "parsing this"
        Bridge::debug als.inspect
        Bridge::debug "--------------------------"

        @a4world = AlloyCompiler.parse(als)
      end

      def fail_if_not_parsed
        fail "model not parsed; call `parse' first" unless @a4world
      end
    end

    module AlloyCompiler
      extend self

      # =================================================================
      # Static, functional-style API (no state carried around)
      # =================================================================
      include Imports
      extend Imports

      # Takes an Alloy model (in Alloy's native als format), parses it
      # into Alloy's native ast form and returns the result.
      #
      # @param als_model [String]
      # @return [Rjb::Proxy ~> CompModule]
      def parse(als_model)
        catch_alloy_errors{ CompUtil_RJB.parseEverything_fromString(@rep, als_model) }
      end

      # Takes a proxy to an Alloy module and an index of a command to
      # execute; executes that command and returns a proxy to an
      # A4Solution object.
      #
      # @param a4world [Rjb::Proxy ~> CompModule]
      # @param cmd_idx_or_name [Int, String] - index or name of the command to execute
      # @param partialInstanceStr [String] - partial instance in a serialized format
      # @return [Rjb::Proxy ~> A4Solution]
      def execute_command(a4world, cmd_idx_or_name=0, partialInstanceStr=nil)
        command_index = case cmd_idx_or_name
                        when Integer
                          cmd_idx_or_name
                        when Symbol, String
                          find_cmd_idx_by_name!(a4world, cmd_idx_or_name)
                        else fail "wrong command type: expected Integer or String, " +
                                  "got #{cmd_idx_or_name}:#{cmd_idx_or_name.class}"
                        end
        commands = a4world.getAllCommands()
        command_index = commands.size + command_index if command_index < 0
        cmd = commands.get(command_index)

        copt = Arby.conf.a4options
        opt = A4Options_RJB.new
        opt.solver = opt.solver.send copt.solver
        (copt.keys - [:solver]).each do |key|
          opt.send "#{key}=", copt[key]
        end
        opt.partialInstance = partialInstanceStr

        Bridge::debug "using command index--"
        Bridge::debug command_index
        Bridge::debug "---------------------"

        Bridge::debug "using bounds---------"
        Bridge::debug partialInstanceStr.inspect
        Bridge::debug "---------------------"
        # Bridge::debug partialInstanceStr

        catch_alloy_errors {
          sigs = a4world.getAllReachableSigs
          rep = Arby.conf.reporter
          rep = Rjb::bind rep, 'edu.mit.csail.sdg.alloy4.IA4Reporter' if rep
          TranslateAlloyToKodkod_RJB.execute_command rep, sigs, cmd, opt
        }
      end

      # Takes a proxy to an Alloy module and returns a flat list of
      # Alloy fields.
      #
      # @param a4world [Rjb::Proxy ~> CompModule]
      # @return [Array(Rjb::Proxy ~> Sig$Field)]
      def all_fields(a4world)
        a4sigs = a4world.getAllReachableSigs
        alloy_fields = []
        num_sigs = a4sigs.size()
        for i in 0...num_sigs
          a4fields = a4sigs.get(i).getFields
          num_fields = a4fields.size
          for i in 0...num_fields
            alloy_fields.push(a4fields.get(i))
          end
        end
        return alloy_fields
        # (0...a4sigs.size).map{ |sig_idx|
        #   a4fields = a4sigs.get(sig_idx).getFields
        #   (0...a4fields.size).map{ |fld_idx|
        #     a4fields.get(fld_idx)
        #   }
        # }.flatten
      end

      def find_cmd_idx_by_name(a4world, cmd_name)
        commands = a4world.getAllCommands
        num_commands = commands.size
        for i in (0...num_commands).to_a.reverse
          return i if cmd_str = commands.get(i).label == cmd_name.to_s
        end
        -1
      end

      def find_cmd_idx_by_name!(a4world, cmd_name)
        idx = find_cmd_idx_by_name(a4world, cmd_name)
        fail "command #{cmd_name} not found" if idx == -1
        idx
      end
    end
  end
end

