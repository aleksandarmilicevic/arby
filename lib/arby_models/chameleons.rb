require 'arby/arby_dsl'

Arby.conf.sym_exe.convert_missing_fields_to_joins = true

module ArbyModels
module ChameleonExample
  extend Arby::Dsl

  alloy :Chameleons do
    sig Time

    enum Color[R, G, B]

    sig Chameleon [
      color: (Color one ** Time),
      meets: (Chameleon lone ** Time)
    ]

    pred change[t1: Time, t2: Time, c: Chameleon] {
      some meets.t1[c] and
      color.t1[c] != color.t1[meets.t1[c]] and
      color.t2[c] == Color - (color.t1[c] + color.t1[meets.t1[c]])
    }

    pred same[t1: Time, t2: Time, c: Chameleon] {
      (no meets.t1[c] or
       color.t1[c] == color.t1[meets.t1[c]]) and
      color.t2[c] == color.t1[c]
    }

    fact inv {
      all(t: Time) { meets.t == ~(meets.t) and no iden & (meets.t) }
    }

    fact changes {
      all(t1: Time) {
        all(t2: t1.next, c: Chameleon) {
          change(t1, t2, c) or same(t1, t2, c)
        }
      }
    }

    pred some_meet { some meets }

    run :some_meet
  end

  alloy :Viz do
    enum Color[Red, Blue, Green, Yellow]
    enum Shape[Box, Circle, Triangle]

    sig Projection [ proj_atoms: univ ]
    sig Node [
      node: (set Projection)
    ]
  end

end
end
