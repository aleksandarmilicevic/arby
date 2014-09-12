require 'arby/arby_dsl'
require 'arby/ast/bounds'

module ArbyModels

module ABZ14
extend Arby::Dsl

  alloy :SBCDES_Total_Observation do
    enum StateSpace(C0_m0, C0_m1, C0_m2)
    enum LocalStateSpace(C0, C1, C2, C3, C4,
                         M0, M1, M2, M3, M4)

    abstract sig Automaton [
      states: (set StateSpace),
      initialState: (one StateSpace),
      markedStates: (set StateSpace)
    ] { 
       initialState.in?(states) and
       markedStates.in?(states)
      }

    one sig Maze5 extends Automaton [
      localStates: (set LocalStateSpace)
    ] {
       states == C0_m0 + C0_m1 + C0_m2 and
       localStates == C0 + C1 + C2 and
       initialState == C0_m2 and
       markedStates == C0_m1 + C0_m0
      }

  pred dummy[a: Automaton] {
       a == Maze5
  }

    run :dummy, 5, Automaton=>exactly(1)
  end
end
end
