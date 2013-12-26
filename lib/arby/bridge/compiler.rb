require 'arby/bridge/imports'
require 'arby/bridge/solution'
require 'sdg_utils/timing/timer'

module Arby
  module Bridge
    class Compiler
      def self.compile(als_model)
        compiler = Compiler.new(als_model)
        compiler.parse
        compiler
      end

      def _a4world
        @a4world
      end

      # @see Compiler.parse
      def parse
        fail "already parsed" if @a4world
        fail "als model not set" unless @als_model
        @a4world = self.class.parse(@als_model)
        self
      end

      # @see Compiler.all_fields
      def all_fields
        fail_if_not_parsed
        self.class.all_fields(@a4world)
      end

      # @see Compiler.execute_command
      def execute_command(cmd_idx_or_name, bounds=nil)
        fail_if_not_parsed
        a4sol = @timer.time_it("execute_command") {
          self.class.execute_command(@a4world, cmd_idx_or_name)
        }
        Solution.new(a4sol, self, @timer.last_time)
      end

      private

      def fail_if_not_parsed
        fail "model not parsed; call `parse' first" unless @a4world
      end

      def initialize(als_model)
        @rep       = nil # we don't care to listen to reports
        @als_model = als_model
        @timer     = SDGUtils::Timing::Timer.new
      end

      # =================================================================
      # Static, functional-style API (no state carried around)
      # =================================================================
      class << self
        include Imports

        # Takes an Alloy model (in Alloy's native als format), parses it
        # into Alloy's native ast form and returns the result.
        #
        # @param als_model [String]
        # @return [Rjb::Proxy ~> CompModule]
        def parse(als_model)
          CompUtil_RJB.parseEverything_fromString(@rep, als_model)
        end

        # Takes a proxy to an Alloy module and an index of a command to
        # execute; executes that command and returns a proxy to an
        # A4Solution object.
        #
        # @param a4world [Rjb::Proxy ~> CompModule]
        # @param cmd_idx_or_name [Int, String] - index or name of the command to execute
        # @return [Rjb::Proxy ~> A4Solution]
        def execute_command(a4world, cmd_idx_or_name=0)
          command_index = case cmd_idx_or_name
                          when Integer
                            cmd_idx_or_name
                          when Symbol, String
                            find_cmd_idx_by_name!(a4world, cmd_idx_or_name)
                          else fail "wrong command type: expected Integer or String, " +
                                    "got #{cmd_idx_or_name}:#{cmd_idx_or_name.class}"
                          end
          commands = a4world.getAllCommands()
          cmd = commands.get(command_index)
          opt = A4Options_RJB.new
          opt.solver = opt.solver.SAT4J #MiniSatJNI #SAT4J
          TranslateAlloyToKodkod_RJB.execute_command(@rep, a4world.getAllSigs, cmd, opt)
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
          for i in 0...num_commands
            return i if cmd_str = commands.get(i).label == cmd_name.to_s
          end
          return -1
        end

        def find_cmd_idx_by_name!(a4world, cmd_name)
          idx = find_cmd_idx_by_name(a4world, cmd_name)
          fail "command #{cmd_name} not found" if idx == -1
          idx
        end

      end
    end
  end
end

