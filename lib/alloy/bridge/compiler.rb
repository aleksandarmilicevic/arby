require 'alloy/bridge/imports'
module Alloy
  module Bridge
    class Compiler
      include Imports

      @@rep = nil # we don't care to listen to reports; 
      
      # Takes an Alloy model (in Alloy's native als format), parses it
      # into Alloy's native ast form and returns the result.
      # 
      # @param als_model [String]
      # @return [Rjb::Proxy ~> CompModule]
      def compute_world(als_model)
        a4world = Imports::CompUtil_RJB.parseEverything_fromString(@@rep, als_model) 
        return a4world
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
        TranslateAlloyToKodkod_RJB.execute_command(@@rep, a4world.getAllSigs, cmd, opt)
      end
      
      # Takes a proxy to an Alloy module and returns a flat list of
      # Alloy fields.
      # 
      # @param a4world [Rjb::Proxy ~> CompModule]
      # @return [Array(Rjb::Proxy ~> Sig$Field)]
      def sigs_fields(a4world)
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

      # Takes a proxy to an Alloy solution and extract a list of all
      # atoms from it.
      # 
      # @param a4sol [Rjb::Proxy ~> A4Solution]
      # @return [Rjb::Proxy ~> SafeList<ExprVar>]
      def flat_list_of_atoms(a4sol)
        return a4sol.getAllAtoms        
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



