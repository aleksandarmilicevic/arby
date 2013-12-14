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

    @@als_model = Arby.meta.to_als
  end

  def test1
    puts @@als_model
  end

end
