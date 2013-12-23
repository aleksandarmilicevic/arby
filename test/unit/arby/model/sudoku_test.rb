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
    Arby.initializer.init_all_no_freeze
  end

  def test_als
    puts Arby.meta.to_als
  end

  def test_instance
    inst = ArbyModels::SudokuModel.find_instance :solved, "for 1 but 5 Int"
    assert inst, "instance not found"
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
    puts s.to_s
    # inst = s.find_instance :solved, "for 1 but 5 Int"
    # puts inst.skolem(inst.skolems.first)
  end
end
