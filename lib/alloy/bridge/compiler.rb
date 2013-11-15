require 'alloy/bridge/imports'
module Alloy
  module Bridge
    class Compiler
      include Imports
      @rep = A4Reporter_RJB.new
      def compute_world(model_string)
        model = model_string
        a4world = Imports::CompUtil_RJB.parseEverything_fromString(@rep, model) 
        return a4world
      end

      def generate_a4solutions(a4world)
        commands = a4world.getAllCommands()
        #if (commands.size != 1) TODO add integer to check this
        #  raise('ErrorAPI_RJB', 'Must specify exactly one command; number of commands found:' + commands.size )
        #end
        cmd = commands.get(0)
        opt = Imports::A4Options_RJB.new

        opt.solver = opt.solver.SAT4J
        a4sol = Imports::TranslateAlloyToKodkod_RJB.execute_command(@rep, a4world.getAllSigs, cmd, opt)
        return a4sol
      end
        
      def sigs_fields(world)
        reachableSigs = world.getAllReachableSigs.size()
        sig = world.getAllReachableSigs
        a4fields = []
        for i in 0...reachableSigs
          fields = sig.get(i).getFields
          if not fields.isEmpty        # should i push empty fields?
            a4fields.push(fields.get(0))#BUG) # BUG
          end
        end
        return a4fields
      end

      def flat_list_of_atoms(a4sol)
        return a4sol.getAllAtoms        
      end

      def list_of_atoms_from_fields(fields,sol) # try either a string or with this iterator 
        a4Tuple_Sets = []
        for i in 0...(fields.size)
          field = fields[i]
          ts = sol.eval(field)
          tsIterator = ts.iterator
          while tsIterator.hasNext
            a4_Tuple = []
            t = tsIterator.next
            arity = t.arity
            for j in 0...(arity)
              a4_Tuple.insert(j,t.atom(j))
            end
            a4Tuple_Sets.insert(i,a4_Tuple)
          end
        end
        return a4Tuple_Sets
      end


    end
  end
end



