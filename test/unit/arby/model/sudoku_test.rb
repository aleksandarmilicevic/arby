require 'my_test_helper'
require 'arby_models/sudoku'
require 'arby/helpers/test/dsl_helpers'
require 'arby/initializer.rb'
require 'arby/bridge/compiler'
require 'arby/bridge/solution'

class SudokuTest < Test::Unit::TestCase
  include Alloy::Helpers::Test::DslHelpers
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions
  include Alloy::Bridge

  include ArbyModels::SudokuModel

  def setup_class
    Alloy.reset
    Alloy.meta.restrict_to(ArbyModels::SudokuModel)
    Alloy.initializer.init_all_no_freeze

    @@als_model = Alloy.meta.to_als
  end

  def test1
    puts @@als_model
  end

end
