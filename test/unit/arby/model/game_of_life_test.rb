require 'my_test_helper'
require 'arby_models/game_of_life'
require 'arby/helpers/test/dsl_helpers'
require 'arby/initializer.rb'
require 'arby/bridge/compiler'
require 'arby/bridge/solution'

class GameOfLifeTest < Test::Unit::TestCase
  include Arby::Helpers::Test::DslHelpers
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions
  include Arby::Bridge

  include ArbyModels::GameOfLife

  def setup_class
    Arby.reset
    Arby.meta.restrict_to(ArbyModels::GameOfLife)
  end

  def test_als
    puts ArbyModels::GameOfLife.to_als
    assert ArbyModels::GameOfLife.compile
  end


end
