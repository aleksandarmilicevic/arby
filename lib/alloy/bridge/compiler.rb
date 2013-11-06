require 'imports'

class compiler
  def compute_world(model_string)
    rep = A4Reporter_RJB.new
    model = model_string
    world = CompUtil_RJB.parseEverything_fromString(rep, model) 
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
    sol = TranslateAlloyToKodkod_RJB.execute_command(rep,world.getAllSigs, cmd, opt)
    return sol
  end

  def SigsFields(world)
    reachableSigs = world.getAllReachableSigs.size()
    for i in 0...reachableSigs
      fields = sig.getFields
    end
    return fields
  end

  def listOfAtoms(fields)
    A4TupleSets =[]
    for i in 0...(fields.size)
      field = fields.get(i)
      ts = sol.eval(field)
      tsIterator = ts.iterator
      A4Tuple =[]
      while tsIterator.hasNext
        t = tsIterator.next
        arity = t.arity
        for j in 0...(arity)
          A4Tuple.insert(j,t.atom(j))
        end
      end
      A4TupleSets.insert(i,A4Tuple)
    end
    return A4TupleSets
  end
end




