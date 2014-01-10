require 'my_test_helper'
require 'arby_models/chameleons'

class ChameleonsTest < Test::Unit::TestCase
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions
  include Arby::Bridge

  include ArbyModels::ChameleonExample::Chameleons

  def setup_class
    Arby.reset
    Arby.meta.restrict_to(ArbyModels::ChameleonExample)
  end

  def test_als
    puts Arby.meta.to_als
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
