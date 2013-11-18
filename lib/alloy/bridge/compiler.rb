require 'alloy/bridge/imports'
module Alloy
  module Bridge
    class Compiler
      include Imports
      @rep = A4Reporter_RJB.new
      
      # Takes an string model for alloy to evaluate,
      # and converts it to a world (an Rjb::proxy -> CompModule) 
      # 
      # @param String
      # @return Rjb::proxy -> CompModule
      def compute_world(model_string)
        model = model_string
        a4world = Imports::CompUtil_RJB.parseEverything_fromString(@rep, model) 
        return a4world
      end

      # Takes an Rjb Proxy object pointing to a world,
      # and generates an Rjb Proxy in the form of an alloy solution
      # 
      # @param a4world [Rjb::proxy -> CompModule]
      # @return [Rjb::proxy -> A4Solution]
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
      
      # Takes an Rjb Proxy object pointing to a world,
      # and generates an arrau with Rjb Proxy in the form of 
      # alloy fields
      # 
      # @param a4world [Rjb::proxy -> CompModule]
      # @return [array[Rjb::proxy -> Sig$Field]
      def sigs_fields(world)
        reachableSigs = world.getAllReachableSigs.size()
        sig = world.getAllReachableSigs
        a4fields = []
        for i in 0...reachableSigs
          fields = sig.get(i).getFields
            a4fields.push(fields) 
        end
        return a4fields
      end

      # Takes an Rjb Proxy of an alloy solution and converts it 
      # to a list of alloy atoms.
      # 
      # @param a4sol [Rjb::Proxy -> A4Solution]
      # @return a4atoms [Rjb::Proxy -> SafeList<ExprVar>]
      def flat_list_of_atoms(a4sol)
        return a4sol.getAllAtoms        
      end

      def list_of_atoms_from_fields(fields,sol) # try either a string or with this iterator 
        a4Tuple_Sets = []
        for i in 0...(fields.size)
          field = fields[i]
            if field.size >0
              for j in 0...(field.size)
                ts = sol.eval(field.get(j))
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
          end
        end
        return a4Tuple_Sets
      end


    end
  end
end



