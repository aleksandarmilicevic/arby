require 'my_test_helper'
require 'arby_models/chameleons'

class ChameleonsTest < Test::Unit::TestCase
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions
  include Arby::Bridge

  include ArbyModels::ChameleonExample
  include ArbyModels::ChameleonExample::Chameleons

  def setup_class
    Arby.reset
    Arby.meta.restrict_to(ArbyModels::ChameleonExample)
  end

  # def test_als
  #   puts ChameleonsViz.meta.to_als.inspect
  # end

  def test_chameleon
    puts Chameleons.meta.to_als
    sol = Chameleons.execute_command :some_meet
    assert sol.satisfiable?
    sol.arby_instance
  end

  def test_viz
    puts Viz.meta.to_als
    inst = Viz.find_instance
    assert inst
  end

  def test_chameleon_viz
    puts ChameleonsViz.meta.to_als
    sol = ChameleonsViz.execute_command :viz
    assert sol.satisfiable?
    sol.arby_instance
  end

  def test_staged
    n = 5
    ch_sol = Chameleons.solve :some_meet, n, Chameleon => exactly(n-1)
    assert ch_sol.satisfiable?
    inst = ch_sol.arby_instance
    bounds = inst.to_bounds
    puts bounds.serialize
    binding.pry
    # viz_sol = ChameleonsViz.solve :viz, bounds, n
  end

  # def test_instance
  #   sol = ArbyModels::Grandpa.execute_command
  #   assert sol.satisfiable?
  #   inst = sol.arby_instance
  #   m = inst["$ownGrandpa_m"]
  #   assert m, "own grandpa skolem not found"
  #   assert m.in? parents(parents(m))
  # end

end
