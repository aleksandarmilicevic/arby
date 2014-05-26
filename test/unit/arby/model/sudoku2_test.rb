require 'my_test_helper'
require 'arby_models/sudoku2'
require 'arby/helpers/test/dsl_helpers'
require 'sdg_utils/timing/timer'

class Sudoku2TestBase < Test::Unit::TestCase
  include Arby::Helpers::Test::DslHelpers
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions

  SudokuModel = ArbyModels.gen_sudoku(4)
  include SudokuModel.ruby_module

  def setup_class
    Arby.reset
    Arby.meta.restrict_to(SudokuModel)
  end

  def test_als
    puts! SudokuModel.meta.to_als
    assert SudokuModel.compile
  end
end
