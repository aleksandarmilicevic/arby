require 'arby/arby_dsl'

# Arby.conf.sym_exe.convert_missing_fields_to_joins = true

module ArbyModels
module ABZ14
module ChameleonExample
  extend Arby::Dsl

  alloy :Chameleons do
    ordered sig Time
    enum Color(R, G, B)

    sig Chameleon [
      color: (Color one ** Time),
      meets: (Chameleon lone ** Time)]

    fact {
      all(t: Time) {
        # meets is symmetric and no one meets oneself
        meets.(t) == ~meets.(t) and no iden & meets.(t) and
        # every time each chameleon changes or stays the same
        all(t2: t.next, c: Chameleon) {
          change(t, t2, c) or same(t, t2, c) }}}

    pred change[t1, t2: Time, c: Chameleon] {
      # at t1 c meets some chameleon with different color;
      some c.meets.(t1) and
      c.color.(t1) != c.meets.(t1).color.(t1) and
      # at t2 it changes color
      c.color.(t2) == Color - (c + c.meets.(t1)).color.(t1) }

    pred same[t1, t2: Time, c: Chameleon] {
      # at t1 c doesn't meet or meets some with same color
      (no c.meets.(t1) or
       c.color.(t1) == c.meets.(t1).color.(t1)) and
      # at t2 it doesn't change color
      c.color.(t2) == c.color.(t1) }

    pred some_meet { some meets }
  end

  alloy :Viz do
    enum Color(Red, Blue, Green, Grey)
    enum Shape(Box, Circle, Triangle)

    ordered sig Projection [
      # atom projected over
      over: univ ]

    sig Node [
      # projections in which appears
      node:  (set Projection),
      # color, shape, and atom for
      # this node in every projection
      color: (Color one ** node),
      shape: (Shape one ** node),
      atom:  (univ  one ** node) ]

    sig Edge [
      # projections in which appears
      edge:   (set Projection),
      # connected nodes
      source: (Node one ** edge),
      dest:   (Node one ** edge) ]

    fact {
      all(p: Projection) {
        # edges in a projection connect
        # nodes in the same projection
        all(e: edge.(p)) {
          enodes = e.(source + dest).(p)
          enodes.in? node.(p) }}}
  end

  alloy :ChameleonsViz do
    open Viz, Chameleons

    pred theme {
      # same ordering of Time and Projection
      Projection::next == over.(Time::next).(~over) and
      # project over Time
      over.in? (Projection ** (one_one Time)) and
      all(t: Time) | let(p: over.(t)) {
        atom.(p).in? (node.(p) ** (one_one Chameleon)) and
        # Viz edges correspond to meets
        meets.(t) == (~source.(p).atom.(p)).dest.(p).atom.(p) and
        all(c: Chameleon) {
          # Viz shape is Box iff it doesn't meet anyone
          (no c.meets.(t)) <=> (atom.(p).(c).shape.(p) == Box) and
          # for every other chameleon
          all(c2: Chameleon - c) {
            # Viz colors for chameleons are the same iff the chameleon are the same at t
            (c.color.(t) == c2.color.(t)) <=> (atom.(p).(c).color.(p) == atom.(p).(c2).color.(p)) and
            # Viz shapes are the same for those chameleons that meet at t
            atom.(p).(c).shape.(p) == atom.(p).(c2).shape.(p) if c.in? c2.meets.(t)
          }}
      } and
      # stability over Time: same colored Chameleons -> same viz colors
      all(t, t2: Time) | all(c, c2: Chameleon) | let(p: over.(t), p2: over.(t2)) {
        atom.(p).(c).color.(p) == atom.(p2).(c2).color.(p2) if t != t2 && c.color.(t) == c2.color.(t2)
      }
    }

    pred viz { some_meet and theme }
  end

end
end
end
