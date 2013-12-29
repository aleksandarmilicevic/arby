require 'my_test_helper'
require 'arby_models/sudoku'
require 'arby/helpers/test/dsl_helpers'
require 'arby/initializer.rb'
require 'arby/bridge/compiler'
require 'arby/bridge/solution'
require 'sdg_utils/timing/timer'

class SudokuTest < Test::Unit::TestCase
  include Arby::Helpers::Test::DslHelpers
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions
  include Arby::Bridge

  include ArbyModels::SudokuModel

  def setup_class
    Arby.reset
    Arby.meta.restrict_to(ArbyModels::SudokuModel)

    @@puzle = """
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
    @@timer = SDGUtils::Timing::Timer.new
  end

  def test_als
    puts Arby.meta.to_als
  end

  def test_instance
    puts "solving sudoku..."
    sol = ArbyModels::SudokuModel.solve :solved, "for 1 but 5 Int"
    puts "solving time: #{sol.solving_time}s"

    assert sol.satisfiable?, "instance not found"
    puts
    @@timer.time_it { puts sol.arby_instance.atoms.first.print }
    puts "print time: #{@@timer.last_time}"
  end

  def test_pi
    s = Sudoku.parse @@puzle
    bounds = s.partial_instance
    assert_equal @@num_given, bounds.get_lower(Sudoku.grid).size
    assert_equal (81-@@num_given)*9 + @@num_given, bounds.get_upper(Sudoku.grid).size
    assert_equal 1, bounds.get_lower(Sudoku).size
    assert_equal 1, bounds.get_upper(Sudoku).size
    assert_equal 10, bounds.get_ints.size
  end

  def test_instance_pi
    s = Sudoku.parse @@puzle

    puts
    @@timer.time_it { puts s.print }
    puts "print time: #{@@timer.last_time}"

    old_grid = s.grid

    puts "solving sudoku with partial instance..."
    sol = ArbyModels::SudokuModel.solve :solved, "", s.partial_instance
    puts "solving time: #{sol.solving_time}s"

    assert sol.satisfiable?, "instance not found"
    assert_equal 81, s.grid.size
    assert old_grid.in?(s.grid)

    a4bounds = sol._a4sol.getBoundsSer
    a4sudoku_bounds = a4bounds.get("this/Sudoku")
    a4grid_bounds = a4bounds.get("this/Sudoku.grid")

    assert_equal 1, a4sudoku_bounds.a.size()
    assert_equal 1, a4sudoku_bounds.b.size()

    assert_equal 26, a4grid_bounds.a.size()
    assert_equal 521, a4grid_bounds.b.size()

    puts
    @@timer.time_it { puts s.print }
    puts "print time: #{@@timer.last_time}"
  end
end
