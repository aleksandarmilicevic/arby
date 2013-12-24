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
  end

  def test_als
    puts Arby.meta.to_als
  end

  def test_instance
    puts "solving sudoku..."
    inst = ArbyModels::SudokuModel.find_instance :solved, "for 1 but 5 Int"
    assert inst, "instance not found"
    puts
    puts inst.atoms.first
  end

  def test_pi
    s = Sudoku.parse """
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
    num_given = 26
    puts
    puts s.to_s
    bounds = s.partial_instance
    assert_equal num_given, bounds.get_lower(Sudoku.grid).size
    assert_equal (81-num_given)*9 + num_given, bounds.get_upper(Sudoku.grid).size

    # inst = s.find_instance :solved, "for 1 but 5 Int"
    # puts inst.skolem(inst.skolems.first)
  end
end
