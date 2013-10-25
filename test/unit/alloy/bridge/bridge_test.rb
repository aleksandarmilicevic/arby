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
Rjb::load('/Users/potter/MIT/4thyear/Fall2013/6uap/alloy/dist/alloy4.2_2013-10-22.jar', ['-Xmx512m', '-Xms256m'])
computil = Rjb::import('edu.mit.csail.sdg.alloy4compiler.parser.CompUtil')
a4rep = Rjb::import('edu.mit.csail.sdg.alloy4.A4Reporter')
str = Rjb::import('java.lang.String')
out = Rjb::import('java.lang.System').out
option = Rjb::import('edu.mit.csail.sdg.alloy4compiler.translator.A4Options')
satSolverClass = Rjb::import('edu.mit.csail.sdg.alloy4compiler.translator.A4Options$SatSolver')


toKodkod = Rjb::import('edu.mit.csail.sdg.alloy4compiler.translator.TranslateAlloyToKodkod')
rep = a4rep.new
modelget = 'sig A {} run {} for 4'
world = computil.parseOneModule(modelget)
world_ReachableSigs = world.getAllReachableSigs
command = world.getAllCommands.get(0)
#binding.pry
options = option.new
options.solver = satSolverClass.SAT4J
binding.pry
ans = toKodkod.execute_command(rep,world_ReachableSigs,command,options)
binding.pry









# #old
# Rjb::load('/Users/potter/MIT/4thyear/Fall2013/6uap/alloy/dist/alloy4.2_2013-10-22.jar')
# Rjb::import('edu.mit.csail.sdg.alloy4viz.VizGUI')
# a4rep = Rjb::import('edu.mit.csail.sdg.alloy4.A4Reporter')
# Rjb::import('import edu.mit.csail.sdg.alloy4.ErrorWarning')
# Rjb::import('java.lang.String')
# out = Rjb::import('java.lang.System').out
# Rjb::import('edu.mit.csail.sdg.alloy4compiler.ast.Module')
# Rjb::import('edu.mit.csail.sdg.alloy4compiler.translator.A4Solution')
# Rjb::import('edu.mit.csail.sdg.alloy4compiler.ast.Command')
# Rjb::import('edu.mit.csail.sdg.alloy4compiler.translator.TranslateAlloyToKodkod')
# Rjb::import('edu.mit.csail.sdg.alloy4.Err')
# #Rjb::load('/Users/potter/MIT/4thyear/Fall2013/6uap/alloy/dist/alloy4.2_2013-10-22.jar', ['-Xmx512m', '-Xms256m'])
# # The visualizer (We will initialize it to nonnull when we visualize an Alloy solution)
# VizGUI viz = null;
# # Alloy4 sends diagnostic messages and progress reports to the A4Reporter.
# #By default, the A4Reporter ignores all these events (but you can extend the A4Reporter to display the event for the user)
# A4Reporter rep = new A4Reporter()
# # not sure what is going on here or how to do this
#     #         @Override public void warning(ErrorWarning msg) {
#     #             System.out.print("Relevance Warning:\n"+(msg.toString().trim())+"\n\n");
#     #             System.out.flush();
#     #         }
#     #     };

# for filename in args [do]  #need to figure out what is filename and args
# 	out.println("=========== Parsing+Typechecking "+filename+" =============")
# 	Module world = CompUtil.parseEverything_fromFile(rep, null, filename);
# 	A4Options options = new A4Options();
# 	options.solver = A4Options.SatSolver.SAT4J;
# 	for Command command in world.getAllCommands() [do]
#    		out.println("============ Command "+command+": ============");
#    		A4Solution ans = TranslateAlloyToKodkod.execute_command(rep, world.getAllReachableSigs(), command, options);
#    		out.println(ans);
#    		if ans.satisfiable
#    			ans.writeXML("alloy_example_output.xml");
#    		end
#    		if viz == null
#    			viz = new VizGUI(false, "alloy_example_output.xml", null);
#    		else
#    			viz.loadXML("alloy_example_output.xml",true);
#    		end
#     end
# end