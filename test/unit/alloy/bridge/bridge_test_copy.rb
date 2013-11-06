require 'test/unit/alloy/bridge/A4Tuple'
# def test_bridge_unit
# 	Rjb::load(classpath = '.', jvmargs=[])
# 	str = Rjb::import('java.lang.String')  # import String class into the varibale 'str'
# 	instance = str.new_with_sig('Ljava.lang.String;', 'hiki is a wiki engine')
# 	s = instance.replaceAll('hiki', 'rwiki')
# 	puts s
# 	assert_equal 1, 1
# end

###
#ExampleUsingTheCompiler
###
#(this cmd should return "nil")
rep = A4Reporter_RJB.new
model = "sig A { f: set A}\n\n run { #f > 1 } for 4"
world = CompUtil_RJB.parseEverything_fromString(rep, model) #TODO model should be passed somehow?
commands = world.getAllCommands()
if (commands.size != 1)
	Rjb::throw('ErrorAPI_RJB', 'Must specify exactly one command; number of commands found:' + commands.size )
end
cmd = commands.get(0)
opt = A4Options_RJB.new

opt.solver = opt.solver.SAT4J
sol = TranslateAlloyToKodkod_RJB.execute_command(rep,world.getAllSigs, cmd, opt)
out.println(sol.to_string)
#binding of the a4soltuon 
for i in 0...(world.getAllReachableSigs.size)
	sig = world.getAllReachableSigs.get(i)
    out.println("traversing sig: " + sig.to_string)
    fields = sig.getFields
    for j in 0...(fields.size)
    	field = fields.get(j)
    	out.println("traversing field: " + field.to_string)
    	ts = sol.eval(field)
        #tuple = A4Tuple.new(ts.iterator.next,sol)
        #binding.pry
        #tuple = Rjb::bind(tuple, 'edu.mit.csail.sdg.alloy4compiler.translator.A4Tuple')
        #binding.pry
        tsIterator = ts.iterator
        binding.pry
        while tsIterator.hasNext
            out.print("    [")
            t = tsIterator.next
            arity = t.arity
            for k in 0...(arity)
                out.print(t.atom(k) + " ")
            end
            out.println("]")
        end
    end
end






