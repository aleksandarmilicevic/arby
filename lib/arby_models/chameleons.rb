require 'arby/arby_dsl'

Arby.conf.sym_exe.convert_missing_fields_to_joins = true

module ArbyModels
module ChameleonExample
  extend Arby::Dsl

  alloy :Viz do
    enum Color(Red, Blue, Green, Yellow)
    enum Shape(Box, Circle, Triangle)

    sig Projection [ proj_atoms: univ ]

    sig Node [
      node:  (set Projection),
      color: (Color one ** node),
      shape: (Shape one ** node),
      atom:  (univ  one ** node)
    ]

    sig Edge [
      edge:   (set Projection),
      source: (Node one ** edge),
      dest:   (Node one ** edge)
    ]

    fact {
      all(p: Projection) {
        all(e: edge.(p)) {
          (source[e] + dest[e]).(p).in? node.(p)
        }
      }
    }
  end


  alloy :Chameleons do
    open Viz

    sig Time

    enum Color(R, G, B)

    sig Chameleon [
      color: (Color one ** Time),
      meets: (Chameleon lone ** Time)
    ]

    pred change[t1: Time, t2: Time, c: Chameleon] {
      cmeets_color_t1 = c.meets.(t1).color.(t1)

      some c.meets.(t1) and
      c.color.(t1) != cmeets_color_t1 and
      c.color.(t2) == Color - (c.color.(t1) + cmeets_color_t1)
    }

    pred same[t1: Time, t2: Time, c: Chameleon] {
      (no c.meets.(t1) or c.color.(t1) == c.meets.(t1).color.(t1)) and
      c.color.(t2) == c.color.(t1)
    }

    fact inv {
      all(t: Time) { meets.(t) == ~meets.(t) and no iden & meets.(t) }
    }

    fact changes {
      all(t1: Time) {
        all(t2: t1.next, c: Chameleon) {
          change(t1, t2, c) or same(t1, t2, c)
        }
      }
    }

    pred some_meet { some meets }

    pred theme {
      # proj_next = proj_atoms.time_next.~proj_atoms
      proj_atoms.in? (Projection one ** (one Time)) and
      all(t: Time) {
        let(p: proj_atoms.(t)) {
          atom.(p).in? (node.(p) ** (one_one Chameleon)) and

          # Viz edges correspond to meets
          meets.(t) == (~source.(p).atom.(p)).dest.(p).atom.(p) and

          all(c: Chameleon) {
            # Viz shape is Box iff it doesn't meet anyone
            (no c.meets.(t)) <=> (atom.(p).(c).shape.(p) == Box) and

            # for every other chameleon
            all(c2: Chameleon - c) {
              # Viz colors are the same iff their colors are the same
              (c.color.(t) == c2.color.(t)) <=>
              (Viz.color.(p)[atom.(p).(c)] == Viz.color.(p)[atom.(p).(c2)]) and

              # Viz shapes are the same for those who meet
              if c.in? c2.meets.(t)
                atom.(p).(c).shape.(p) == atom.(p).(c2).shape.(p)
              end
            }
          }

        }
      } and

      # stability over Time: same colored Chameleons -> same viz colors
      all(t: Time, t2: Time, c: Chameleon, c2: Chameleon) {
        let(p: proj_atoms.(t), p2: proj_atoms.(t2)) {
          if t != t2 and c.color.(t) == c2.color.(t2)
            atom.(p).(c).color.(p) == atom.(p2).(c2).color.(p2)
          end
        }
      }
    }

    run :some_meet
  end

end
end
