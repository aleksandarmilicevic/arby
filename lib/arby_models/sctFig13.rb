require 'arby/arby_dsl'
require 'arby/ast/bounds'

module ArbyModels
       extend Arby::Dsl

  alloy :SBCDES_Total_Observation do
    enum StateSpace(X0, X1, X2, X3, X4, X5, X6, X7, X8, X9)
    enum EventSet(E0, E1, E2, E3, E4, E5, E6, E7, E8, E9)
    enum LocalStateSpace(X10, X11)

    abstract sig Automaton [
      states: (set StateSpace),
      initialState: (one StateSpace),
      markedStates: (set StateSpace),
      events: (set EventSet),
      ctrlEvents: (set EventSet),
      transition: (set StateSpace ** EventSet ** StateSpace)
    ] { 
       initialState.in?(states) and
       markedStates.in?(states) and
       ctrlEvents.in?(events)
      }

    one sig A extends Automaton [
       localStates: (set LocalStateSpace)
    ] {
       states == X0 + X1 + X2 + X3 + X4 + X5 + X6 + X7 + X8 + X9 and
       initialState == X0 and
       markedStates == X1 + X4 + X6 + X9 and
       events == E0 + E1 + E2 + E3 + E4 + E5 + E6 + E7 + E8 + E9 and
       ctrlEvents == E2 + E4 + E7 + E8 + E9 and
       transition == X0 ** E1 ** X1 + X0 ** E2 ** X2 + X0 ** E6 ** X6 +
                     X1 ** E0 ** X0 + 
                     X2 ** E3 ** X3 + X3 ** E4 ** X4 + X4 ** E5 ** X5 +
                     X6 ** E7 ** X7 +
                     X8 ** E9 ** X9 + X9 ** E8 ** X8 and
       localStates == X10 + X11
      }

    fun getInitialState[g: (one Automaton)] [(one StateSpace)] {
        g.initialState
    }

    fun getMarkedStates[g: (one Automaton)] [(set StateSpace)] {
        g.markedStates
    }

    fun getSrcStates[g: (one Automaton)] [(set StateSpace)] {
        ((g.transition).(g.states)).(g.events)
    }

    fun getSrcStatesBug[g: (one Automaton)] [(set EventSet)] {
        ((g.transition).(g.states)).(g.events)
    }

    fun getDstStates[g: (one Automaton)] [(set StateSpace)] {
        (g.events).((g.states).(g.transition))
    }

    fun getEvt[g: (one Automaton)] [(set EventSet)] {
        ((g.states).(g.transition)).(g.states)
    }

    fun getSrcEvt[g: (one Automaton)] [(set StateSpace**EventSet)] {
        (g.transition).(g.states)
    }

    fun getEvtDst[g: (one Automaton)] [(set EventSet**StateSpace)] {
        (g.states).(g.transition)
    }

    fun getM1States[g: (one A)] [(set StateSpace)] {
        (StateSpace).select { |x| x.in?(g.markedStates) }
    }

    fun getM2States[g: (one Automaton)] [(set StateSpace**StateSpace)] {
        (StateSpace**StateSpace).select{|x,y| x.in?(g.markedStates) and y==g.initialState}
    }

#    fun getEvtSrcDst[g: (one Automaton)] [(set EventSet**StateSpace**StateSpace)] {
#        (EventSet ** StateSpace ** StateSpace).select { |x, y, z|
#          x.in?(g.events) and
#          y.in?(g.states) and
#          z.in?(g.states) and
#          (y ** x ** z).in?(g.transition)}
#    }


  pred dummy[a: Automaton] {
       a == A
  }

  pred instance[] {}
  run :instance, 5

  run :dummy, 5, Automaton=>exactly(1)
  end
end
