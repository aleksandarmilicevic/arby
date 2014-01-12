require 'arby/arby_dsl'

# Arby.conf.sym_exe.convert_missing_fields_to_joins = true

module ArbyModels
module ChameleonExample
  extend Arby::Dsl

  alloy :Viz do
    enum Color(Red, Blue, Green, Grey)
    enum Shape(Box, Circle, Triangle)

    ordered sig Projection [ pr_atoms: univ ]

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
          e.(source + dest).(p).in? node.(p)
        }
      }
    }
  end

  alloy :Chameleons do
    ordered sig Time

    enum Color(R, G, B)

    sig Chameleon [
      color: (Color one ** Time),
      meets: (Chameleon lone ** Time)
    ]

    pred change[t1: Time, t2: Time, c: Chameleon] {
      cmeets = c.meets.(t1)

      some c.meets.(t1) and
      c.color.(t1) != cmeets.color.(t1) and
      c.color.(t2) == Color - (c + cmeets).color.(t1)
    }

    pred same[t1: Time, t2: Time, c: Chameleon] {
      (no c.meets.(t1) or
       c.color.(t1) == c.meets.(t1).color.(t1)) and
      c.color.(t2) == c.color.(t1)
    }

    fact inv {
      all(t: Time) { meets.(t) == ~meets.(t) and no iden & meets.(t) }
    }

    fact changes {
      all(t1: Time) | all(t2: t1.next, c: Chameleon) {
        change(t1, t2, c) or same(t1, t2, c)
      }
    }

    pred some_meet { some meets }
    run :some_meet
  end

  alloy :ChameleonsViz do
    open Viz, Chameleons

    pred theme {
      # same ordering of Time and Projection
      Projection::next == pr_atoms.(Time::next).(~pr_atoms) and

      # project over Time
      pr_atoms.in? (Projection one ** (one Time)) and

      all(t: Time) | let(p: pr_atoms.(t)) {
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
            (atom.(p).(c).color.(p) == atom.(p).(c2).color.(p)) and

            # Viz shapes are the same for those who meet
            if c.in? c2.meets.(t)
              atom.(p).(c).shape.(p) == atom.(p).(c2).shape.(p)
            end
          }
        }
      } and

      # stability over Time: same colored Chameleons -> same viz colors
      all(t: Time, t2: Time, c: Chameleon, c2: Chameleon) |
        let(p: pr_atoms.(t), p2: pr_atoms.(t2)) {
          if t != t2 and c.color.(t) == c2.color.(t2)
            atom.(p).(c).color.(p) == atom.(p2).(c2).color.(p2)
          end
      }
    }

    pred viz { some_meet and theme }
    run :viz, 6, Chameleon => (exactly 5)
  end

end
end
