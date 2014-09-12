require 'my_test_helper'
require 'arby_models/sct0'

class ABZ14SCTTest < Test::Unit::TestCase
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions
  include Arby::Bridge

  SBCDES_Total_Observation = ArbyModels::ABZ14::SBCDES_Total_Observation
  include SBCDES_Total_Observation

  def setup_class
    puts "Setup ..."
    Arby.reset
    Arby.meta.restrict_to(ArbyModels::ABZ14::SBCDES_Total_Observation)
  end

  def test_als
    puts! "Compiling ..."
    # assert SBCDES_Total_Observation.compile
    # puts! SBCDES_Total_Observation.to_als

    SBCDES_Total_Observation.find_instance
  end

  def test_exe_spec
    puts! SBCDES_Total_Observation.meta.to_als
    puts! "Execution ..."
  end

  def test_run
    puts! "Execute run command ..."
    sol = SBCDES_Total_Observation.run_dummy
    assert sol.satisfiable?
    a = sol["$dummy_a"]
    puts! a.states
    puts! a.localStates
    print "Initial state: "
    puts! a.initialState
    puts! a.markedStates
  end
end
