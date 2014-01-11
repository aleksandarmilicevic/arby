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
      edge:     (set Projection),
      relation: (univ one ** edge),
      source:   (Node one ** edge),
      dest:     (Node one ** edge)
    ]

    fact {
      all(p: Projection, e: edge.p) {
        (e.source + e.dest).p.in? node.p
      }
    }
  end


  alloy :Chameleons do
    #open Viz
    include Viz
    extend Viz
    ::Viz = Viz

    sig Time

    enum Color(R, G, B)

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

    pred theme {
      # proj_next = proj_atoms.time_next.~proj_atoms
      proj_atoms.in? (Projection one ** (one Time)) and
      all(t: Time) {
        let(p: proj_atoms.t) {
          atom.p.in? (node.p one ** (one Chameleon))
          all(c1: Chameleon) {
            all(c2: Chameleon - c1) {
              (c1.color.t == c2.color.t) <=>
              (Viz.color.p[atom.p.c1] == Viz.color.p[atom.p.c2]) and
              ((shape.p[atom.p.c1] == shape.p[atom.p.c2]) if c1.in?(c2.meets.t))
            }
          }
        }
      }
    }

    run :some_meet
  end

end
end
