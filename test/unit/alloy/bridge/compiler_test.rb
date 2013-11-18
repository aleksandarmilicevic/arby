require 'my_test_helper'
require 'alloy/bridge/compiler'

module Alloy
  module Bridge

    class CompilerTest < Test::Unit::TestCase
      def test_compiler
        model = "sig A { f: set A}\n\n run { #f > 1 && #A = 2 } for 4"
        compiler = Compiler.new
        a4world = compiler.compute_world(model)
        a4sol = compiler.execute_command(a4world)
        a4fields = compiler.sigs_fields(a4world)
        a4atoms = compiler.flat_list_of_atoms(a4sol)
        assert_equal 2, a4atoms.size
        assert_equal "A$0", a4atoms.get(0).toString
        assert_equal "A$1", a4atoms.get(1).toString
        # atoms = compiler.list_of_atoms_from_fields(fields, sol)
        # assert_equal atoms.size, 2
        # assert_equal atoms[0].size, 2
        # assert_equal atoms[1].size, 2
        # assert_equal atoms[0], ["A$1", "A$1"]
        # assert_equal atoms[1], ["A$1", "A$0"]
      end
    end
  end
end
