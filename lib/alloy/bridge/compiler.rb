require '/Users/potter/MIT/4thyear/Fall2013/6uap/arby/lib/alloy/bridge/imports'

class Compiler
  @rep = A4Reporter_RJB.new
  def compute_world(model_string)
    model = model_string
    world = CompUtil_RJB.parseEverything_fromString(@rep, model) 
    return world
  end

  def generate_A4Solutions(world)
    commands = world.getAllCommands()
    #if (commands.size != 1)
    #  Rjb::throw('ErrorAPI_RJB', 'Must specify exactly one command; number of commands found:' + commands.size )
    #end
    cmd = commands.get(0)
    opt = A4Options_RJB.new

    opt.solver = opt.solver.SAT4J
    sol = TranslateAlloyToKodkod_RJB.execute_command(@rep,world.getAllSigs, cmd, opt)
    return sol
  end

  def SigsFields(world)
    reachableSigs = world.getAllReachableSigs.size()
    for i in 0...reachableSigs
      sig = world.getAllReachableSigs.get(i)
      fields = sig.getFields
    end
    return fields
  end

  def listOfAtoms(fields,sol)
    a4Tuple_Sets = []
    for i in 0...(fields.size)
      field = fields.get(i)
      ts = sol.eval(field)
      tsIterator = ts.iterator
      a4_Tuple = Array.new
      while tsIterator.hasNext
        t = tsIterator.next
        arity = t.arity
        for j in 0...(arity)
          a4_Tuple.insert(j,t.atom(j))
        end
      end
      a4Tuple_Sets.insert(i,a4_Tuple)
    end
    return a4Tuple_Sets
  end
end




