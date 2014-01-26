require 'arby/bridge/imports'
require 'arby/bridge/solution'
require 'sdg_utils/timing/timer'

module Arby
  module Bridge
    class Compiler
      # @model     [Arby::Ast::Model]
      # @als_model [String]
      def self.compile(model, als_model=nil)
        als_model, model = [model, nil] if als_model.nil? && model.is_a?(String)
        compiler = Compiler.new(model, als_model || model.to_als)
        compiler.parse
        compiler
      end

      def model() @model end
      def _a4world() @a4world end

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
      # @result [Arby::Bridge::Solution]
      def execute_command(cmd_idx_or_name=0, bounds=nil)
        fail_if_not_parsed
        univ = bounds && bounds.extract_universe
        pi = bounds && bounds.serialize(univ)

        puts "solving this"
        puts @als_model
        puts "--------------------------"

        a4sol = @timer.time_it("execute_command") {
          self.class.execute_command(@a4world, cmd_idx_or_name, pi)
        }
        sol = Solution.new(a4sol, self, univ, bounds, @timer.last_time)
        sol.arby_instance if univ && !univ.sig_atoms.empty?
        sol
      end

      private

      def fail_if_not_parsed
        fail "model not parsed; call `parse' first" unless @a4world
      end

      def initialize(model, als_model)
        @model     = model
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
          opt = A4Options_RJB.new
          opt.solver = opt.solver.MiniSatJNI #SAT4J #MiniSatJNI
          opt.renameAtoms = false
          opt.partialInstance = partialInstanceStr

          # puts "using command index--"
          # puts command_index
          # puts "---------------------"

          puts "using bounds---------"
          puts partialInstanceStr.inspect
          puts "---------------------"
          puts partialInstanceStr



          catch_alloy_errors {
            sigs = a4world.getAllReachableSigs
            TranslateAlloyToKodkod_RJB.execute_command @rep, sigs, cmd, opt
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
end

