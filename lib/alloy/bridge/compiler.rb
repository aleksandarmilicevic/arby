require 'alloy/bridge/imports'
module Alloy
  module Bridge
    class Compiler
      def self.compile(als_model)
        compiler = Compiler.new(als_model)
        compiler.parse
        compiler
      end

      def parse
        fail "already parsed" if @a4world
        fail "als model not set" unless @als_model
        @a4world = self.class.parse(@als_model)
        self
      end

      def all_fields
        fail_if_not_parsed
        self.class.all_fields(@a4world)
      end

      def execute_command(cmd_idx)
        fail_if_not_parsed
        a4sol = self.class.execute_command(@a4world)
        Solution.new(a4sol)
      end

      def map_tuples_to_fields(a4fields,a4sol)
         map = self.class.map_tuples_to_fields(a4fields,a4sol)
      end
      private

      def fail_if_not_parsed
        fail "model not parsed; call `parse' first" unless @a4world
      end

      def initialize(als_model)
        @rep       = nil # we don't care to listen to reports
        @als_model = als_model
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
        # @param command_index [Int] - index of the command to execute
        # @return [Rjb::Proxy ~> A4Solution]
        def execute_command(a4world, command_index=0)
          commands = a4world.getAllCommands()
          cmd = commands.get(command_index)
          opt = A4Options_RJB.new
          opt.solver = opt.solver.SAT4J
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
            a4Fields = a4sigs.get(i).getFields
            num_fields = a4Fields.size
            for i in 0...num_fields
              alloy_fields.push(a4Fields.get(i))
            end
          end
          return alloy_fields
        end

        def map_tuples_to_fields(a4fields,a4sol)
          tuples_to_fields = Hash.new

          for i in 0...(a4fields.size)
            field = a4fields[i]
            key = field.label
            ts = a4sol.get_sol.eval(field)
            tsIterator = ts.iterator
            a4_Tuples = []
            while tsIterator.hasNext
              t = tsIterator.next
              a4_Tuple = []
              for j in 0...(t.arity)
                #TO DO look in the API for the ExprVar over the string
                a4_Tuple.push(t.atom(j))
              end
              a4_Tuples.push(a4_Tuple)
            end
            tuples_to_fields[key] =  a4_Tuples
          end

          tuples_to_fields
        end

      end

    end
  end
end

