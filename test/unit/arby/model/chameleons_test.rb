require 'my_test_helper'
require 'arby_models/chameleons'

class ChameleonsTest < Test::Unit::TestCase
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions
  include Arby::Bridge

  include ArbyModels::ChameleonExample

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
  end

  def test_chameleon_viz
    puts ChameleonsViz.meta.to_als
    sol = ChameleonsViz.execute_command :viz
    assert sol.satisfiable?
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
