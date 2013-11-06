require 'rjb'
require 'pry'

Rjb::load('/Users/potter/MIT/4thyear/Fall2013/6uap/alloy/dist/alloy4.2_2013-11-02.jar', ['-Xmx512m', '-Xms256m'])

Type_RJB = Rjb::import('edu.mit.csail.sdg.alloy4compiler.ast.Type')
SigPrimSig_RJB = Rjb::import('edu.mit.csail.sdg.alloy4compiler.ast.Sig$PrimSig')
Tuple_RJB = Rjb::import('kodkod.instance.Tuple')
str = Rjb::import('java.lang.String')
out = Rjb::import('java.lang.System').out
itr = Rjb::import('java.lang.Iterable')

class A4Tuple

end


# class Comparable
#   def initialize(val)
#     @value = val
#   end
#   def compareTo(oponent)
#     return @value - oponent.to_i
#   end
# end
# cp = Comparable.new(3)
# cp = Rjb::bind(cp, 'java.lang.Comparable')
# bind(obj, name)
# bind ruby object and Java interface
# obj
# ruby object
# name
# Java's interface name
# return
# new object that's bound to the specified interface




# rep = A4Reporter_RJB.new
# model = "sig A { f: set A}\n\n run { #f > 1 } for 4"
# world = CompUtil_RJB.parseEverything_fromString(rep, model) #TODO model should be passed somehow?
# commands = world.getAllCommands()
# if (commands.size != 1)
# 	Rjb::throw('ErrorAPI_RJB', 'Must specify exactly one command; number of commands found:' + commands.size )
# end
# cmd = commands.get(0)
# opt = A4Options_RJB.new

# opt.solver = opt.solver.SAT4J
# sol = TranslateAlloyToKodkod_RJB.execute_command(rep,world.getAllSigs, cmd, opt)
# out.println(sol.to_string)
# #binding of the a4soltuon 
# for i in 0...(world.getAllReachableSigs.size)
# 	sig = world.getAllReachableSigs.get(i)
#     out.println("traversing sig: " + sig.to_string)
#     fields = sig.getFields
#     for j in 0...(fields.size)
#     	field = fields.get(j)
#     	out.println("traversing field: " + field.to_string)
#     	ts = sol.eval(field)
#         tsIterator = ts.iterator
#         while tsIterator.hasNext
#             out.print("    [")
#             t = tsIterator.next
#             arity = t.arity
#             for k in 0...(arity)
#                 out.print(t.atom(k) + " ")
#             end
#             out.println("]")
#         end
#     end
# end






