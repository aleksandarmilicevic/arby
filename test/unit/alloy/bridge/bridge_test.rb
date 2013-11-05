require 'rjb'
require 'pry'

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
Rjb::load('/Users/potter/MIT/4thyear/Fall2013/6uap/alloy/dist/alloy4.2_2013-11-02.jar', ['-Xmx512m', '-Xms256m'])

A4Reporter_RJB = Rjb::import('edu.mit.csail.sdg.alloy4.A4Reporter')
CompUtil_RJB = Rjb::import('edu.mit.csail.sdg.alloy4compiler.parser.CompUtil')
ConstList_RJB = Rjb::import('edu.mit.csail.sdg.alloy4.ConstList')
Err_RJB = Rjb::import('edu.mit.csail.sdg.alloy4.Err')
ErrorAPI_RJB = Rjb::import('edu.mit.csail.sdg.alloy4.ErrorAPI')
SafeList_RJB = Rjb::import('edu.mit.csail.sdg.alloy4.SafeList')
Command_RJB = Rjb::import('edu.mit.csail.sdg.alloy4compiler.ast.Command')
SigField_RJB = Rjb::import('edu.mit.csail.sdg.alloy4compiler.ast.Sig$Field')
parser_CompModule_RJB= Rjb::import('edu.mit.csail.sdg.alloy4compiler.parser.CompModule')
A4Options_RJB = Rjb::import('edu.mit.csail.sdg.alloy4compiler.translator.A4Options')
A4Solution_RJB = Rjb::import('edu.mit.csail.sdg.alloy4compiler.translator.A4Solution')
A4Tuple_RJB = Rjb::import('edu.mit.csail.sdg.alloy4compiler.translator.A4Tuple')
A4TupleSet_RJB = Rjb::import('edu.mit.csail.sdg.alloy4compiler.translator.A4TupleSet')
TranslateAlloyToKodkod_RJB = Rjb::import('edu.mit.csail.sdg.alloy4compiler.translator.TranslateAlloyToKodkod')
str = Rjb::import('java.lang.String')
out = Rjb::import('java.lang.System').out
itr = Rjb::import('java.lang.Iterable')

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

for i in 0..(world.getAllReachableSigs.size-1)
	sig = world.getAllReachableSigs.get(i)
    out.println("traversing sig: " + sig.to_string)
    fields = sig.getFields
    for j in 0..(fields.size  - 1)
    	field = fields.get(j)
    	out.println("traversing field: " + field.to_string)
    	ts = sol.eval(field)
        tsIterator = ts.iterator
        while tsIterator.hasNext
            out.print("    [")
            t = tsIterator.next
            arity = t.arity
            for k in 0...(arity -1)
                out.print(t.atom(k) + " ")
            end
            out.println("]")
        end
    end
end






