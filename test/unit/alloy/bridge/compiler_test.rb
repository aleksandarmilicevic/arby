require 'my_test_helper'
require 'alloy/bridge/compiler'

module Alloy
  module Bridge

    class CompilerTest < Test::Unit::TestCase
      def test_compiler
        model = "sig A { f: set A}\n\n run { #f > 1 } for 4"
        compiler = Compiler.new
        world = compiler.compute_world(model)
        sol = compiler.generate_a4solutions(world)
        fields = compiler.sigs_fields(world)
        # atoms = compiler.flat_list_of_atoms(sol)
        atoms = compiler.list_of_atoms_from_fields(fields, sol)
        assert_equal atoms.size, 2
        assert_equal atoms[0].size, 2
        assert_equal atoms[1].size, 2
        assert_equal atoms[0], ["A$1", "A$1"]
        assert_equal atoms[1], ["A$1", "A$0"]
      end
    end
  end
end
