require 'arby/arby_dsl'
require 'arby/ast/bounds'
require 'arby_models/synth/synth2'

module ArbyModels::Synth
  extend Arby::Dsl

  alloy :ParityAigD0 do
    open Synth2

    # ---------
    # -- Vars
    # ---------

    one sig A, B, C, D < BoolVar

    # ---------
    # -- Spec
    # ---------
    fun parity[a: Bit, b: Bit, c: Bit, d: Bit][Bit] {
"""
  Xor[Not[Xor[a, b]], Not[Xor[c, d]]]
"""
    }

    pred spec[root: Node, eval: Node.e ** (Int + Bit)] {
"""
  let a = eval[A], b = eval[B], c = eval[C], d = eval[D] |
    parity[a, b, c, d] = And[eval[root],
                             Not[And[And[Not[And[a, b]],
                                     Not[And[Not[a], Not[b]]]],
                                 And[Not[And[Not[c], Not[d]]],
                                     Not[And[c, d]]]]]]
"""
    }

    run :synthBoolNode, 3, Int=>-1..0, Nand=>exactly(5), Not=>exactly(4), And=>exactly(2),
                                   ITE=>0, IntVar=>0, IntLit=>0, Nor=>0, AndInv => 0, OrInv => 0,
                                   GT=>0, GTE=>0, LT=>0, LTE=>0, Equals=>0, Or=>0

    run :synthBoolNode, 3, Int=>-1..0,  AndInv => exactly(7), Nand=>0, Not=>0, And=>0,
                                   ITE=>0, IntVar=>0, IntLit=>0, Nor=>0, OrInv => 0,
                                   GT=>0, GTE=>0, LT=>0, LTE=>0, Equals=>0, Or=>0
  end
end
