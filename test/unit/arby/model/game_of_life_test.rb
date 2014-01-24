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

  def test_blinker
    c1 = Cell.new :x => -1, :y => 0
    c2 = Cell.new :x =>  0, :y => 0
    c3 = Cell.new :x =>  1, :y => 0
    cells = [c1, c2, c3]
    w = World.new :cells => cells
    wn = World.new

    bnds = Arby::Ast::Bounds.new
    bnds.bound(World, [w, wn])
    bnds.lo[Cell.x] = w.cells.(:x)
    bnds.lo[Cell.y] = w.cells.(:y)
    bnds.lo[World.cells] = w ** w.cells
    # sol = ArbyModels::GameOfLife.solve bnds {
    #   tick(w, wn)
    # }
    puts bnds.serialize
    sol = ArbyModels::GameOfLife.solve :tick, bnds
  end

end
