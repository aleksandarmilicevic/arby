require 'my_test_helper'
require 'arby_models/sudoku'
require 'arby/helpers/test/dsl_helpers'
require 'arby/initializer.rb'
require 'arby/bridge/compiler'
require 'arby/bridge/solution'

class SudokuTest < Test::Unit::TestCase
  include Arby::Helpers::Test::DslHelpers
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions
  include Arby::Bridge

  include ArbyModels::SudokuModel

  def setup_class
    Arby.reset
    Arby.meta.restrict_to(ArbyModels::SudokuModel)

    @@s = Sudoku.parse """
......95.
.8.7..6..
4...68...
3...5.7.2
...9.4...
2.6.1...5
...18...9
..2..3.6.
.35......
"""
    @@num_given = 26
  end

  def test_als
    puts Arby.meta.to_als
  end

  def test_instance
    puts "solving sudoku..."
    sol = ArbyModels::SudokuModel.solve :solved, "for 1 but 5 Int"
    puts "solving time: #{sol.solving_time}s"

    assert sol.satisfiable?, "instance not found"
    # puts
    # puts sol.arby_instance.atoms.first.print
  end

  def test_pi
    # puts
    # puts @@s.print
    bounds = @@s.partial_instance
    # puts bounds.serialize
    assert_equal @@num_given, bounds.get_lower(Sudoku.grid).size
    assert_equal (81-@@num_given)*9 + @@num_given, bounds.get_upper(Sudoku.grid).size
    assert_equal 1, bounds.get_lower(Sudoku).size
    assert_equal 1, bounds.get_upper(Sudoku).size
    assert_equal 10, bounds.get_ints.size
  end

  def test_instance_pi
    puts "solving sudoku with partial instance..."
    sol = ArbyModels::SudokuModel.solve :solved, "for 1 but 5 Int", @@s.partial_instance
    puts "solving time: #{sol.solving_time}s"

    assert sol.satisfiable?, "instance not found"
    # puts
    # puts sol.arby_instance.atoms.first.print
  end
end
