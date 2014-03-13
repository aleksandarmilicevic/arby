require 'arby/arby_dsl'
require 'arby/ast/bounds'

module ArbyModels
  extend Arby::Dsl

  alloy :SynthJoe do

    # --------------------------------------------------------------------------------
    # -- Variables and Values
    # --------------------------------------------------------------------------------
    abstract sig Boolean
    one sig BoolTrue extends Boolean
    one sig BoolFalse extends Boolean

    # --------------------------------------------------------------------------------
    # -- AST Nodes
    # --------------------------------------------------------------------------------
    abstract sig Node
    abstract sig IntNode extends Node

    sig ITE extends IntNode [
      condition: BoolNode,
      then: IntNode,
      elsen: IntNode
    ]

    abstract sig BoolNode extends Node
    sig GTE extends BoolNode [
      left, right: IntNode
    ]

    abstract sig Var extends IntNode
    one sig X, Y, Z < Var

    # --------------------------------------------------------------------------------
    # -- Semantics
    # --------------------------------------------------------------------------------
    pred semantics[eval: Node.e ** (Int + Boolean)] {
      all(n: ITE) {
        eval[n].in? Int and
        eval[n.condition].in? Boolean and
        eval[n.then].in? Int and
        eval[n.elsen].in? Int and
        if eval[n.condition] == BoolTrue
          eval[n.then] == eval[n]
        else
          eval[n.elsen] == eval[n]
        end
      } and

      all(n: GTE) {
        eval[n].in? Boolean and
        eval[n.left].in? Int and
        eval[n.right].in? Int and
        # eval[n.left] >= eval[n.right] <=> eval[n] = BoolTrue
        # not(eval[n.left] >= eval[n.right]) <=> eval[n] = BoolFalse
        if eval[n.left] >= eval[n.right]
          eval[n] == BoolTrue
        else
          eval[n] == BoolFalse
        end
      } and

      all(v: Var) { eval[v].in? Int } and
      eval[X].in? Int and
      eval[Y].in? Int and
      eval[Z].in? Int
    }

    # --------------------------------------------------------------------------------
    # -- Property
    # --------------------------------------------------------------------------------
    pred irreflexive[r: univ ** univ] { no (iden & r) }

    pred acyclic[r: univ ** univ, s: (set univ)] {
      all(x: s) { not x.in?(x.^r) }
    }

    fact {
      acyclic(condition + ITE.then + elsen + left + right, Node)
    }

    $pera = 1
    binding.pry
    pred spec[root: Node, eval: Node.e ** (Int + Boolean)] {
      eval[root] >= eval[X] and
      eval[root] >= eval[Y] and
      eval[root] >= eval[Z] and
      (eval[root] == eval[X] or
         eval[root] == eval[Y] or
           eval[root] == eval[Z])
    }

    # pred program[root: Node] {
    #   root.in? ITE and

    #   root.condition.in? GTE and
    #   root.condition.left == X and
    #   root.condition.right == Y and

    #   root.then.in? ITE and

    #   root.then.condition.in? GTE and
    #   root.then.condition.left == X and
    #   root.then.condition.right == Z and

    #   root.then.then == X and
    #   root.then.elsen == Z and

    #   root.elsen.in? ITE and

    #   root.elsen.condition.in? GTE and
    #   root.elsen.condition.left == Y and
    #   root.elsen.condition.right == Z and

    #   root.elsen.then == Y and
    #   root.elsen.elsen == Z and
    # }

    pred synth_max3 {
      some(root: IntNode) {
        # program[root]
        all(eval: Node.e ** (Int + Boolean)) {
          spec(root, eval) if semantics(eval)
        }
      }
    }

    run :synth_max3, 9, Int => 2
  end
end
