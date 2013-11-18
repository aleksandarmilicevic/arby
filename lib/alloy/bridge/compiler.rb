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

        # def list_of_atoms_from_fields(fields,sol) # try either a string or with this iterator 
        #   a4Tuple_Sets = []
        #   for i in 0...(fields.size)
        #     field = fields[i]
        #     ts = sol.eval(field)
        #     tsIterator = ts.iterator
        #     while tsIterator.hasNext
        #       a4_Tuple = []
        #       t = tsIterator.next
        #       arity = t.arity
        #       for j in 0...(arity)
        #         a4_Tuple.insert(j,t.atom(j))
        #       end
        #       a4Tuple_Sets.insert(i,a4_Tuple)
        #     end
        #   end
        #   return a4Tuple_Sets
        # end
      end

    end
  end
end



