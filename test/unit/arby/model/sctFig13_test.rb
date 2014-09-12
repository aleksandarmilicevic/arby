require 'my_test_helper'
require 'arby_models/sctFig13'

class ABZ14SCTTest < Test::Unit::TestCase
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions
  include Arby::Bridge

  SBCDES_Total_Observation = ArbyModels::SBCDES_Total_Observation
  include SBCDES_Total_Observation

  def test_run
    puts "Execute run command ..."
#    SBCDES_Total_Observation.find_instance nil, 5, Automaton=>exactly(1)
#   sol = SBCDES_Total_Observation.run_instance
    sol = SBCDES_Total_Observation.run_dummy
#     sol.fail_if_unsat  # This is a private method that work well.
     puts sol.solving_time
     assert sol.satisfiable?
    a = sol["$dummy_a"]
    print "States: "
    puts! a.states
    print "*** NOW it's work with the new version ---- Local states: "
    puts! a.localStates
    print "Initial state: "
    puts! a.initialState
    print "Marked states: "
    puts! a.markedStates
    print "Events: "
    puts! a.events
    print "Controllable events: "
    puts! a.ctrlEvents
    print "Transition function: "
    puts! a.transition
    print "Initial state (again): "
    puts! getInitialState(a)
    print "Marked states (again): "
    puts! getMarkedStates(a)
    print "Source states: "
    puts! getSrcStates(a)
    print "Source states (Surprisingly it's worked even though the function should return a set of events!!!: "
    puts! getSrcStatesBug(a)
    print "A binary relation (source -- event): "
    puts! getSrcEvt(a)
    print "A unary relation for test: "
    puts! getM1States(a)
    print "A binary relation for test: "
    puts! getM2States(a)
end
end
