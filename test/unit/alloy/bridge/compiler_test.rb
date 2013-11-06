require 'my_test_helper'
require '/Users/potter/MIT/4thyear/Fall2013/6uap/arby/lib/alloy/bridge/compiler'

class CompilerTest < Test::Unit::TestCase

    def test_compiler
        model = "sig A { f: set A}\n\n run { #f > 1 } for 4"
        compiler = Compiler.new
        world = compiler.compute_world(model)
        sol = compiler.generate_A4Solutions(world)
        fields = compiler.SigsFields(world)
        atoms = compiler.listOfAtoms(fields,sol)
        assert_equal atoms.size , 2
        assert_equal atoms[0].size , 2
        assert_equal atoms[1].size , 2
        assert_equal atoms[0] , ["A$1", "A$1"]
        assert_equal atoms[1] , ["A$1", "A$0"]
    end
end