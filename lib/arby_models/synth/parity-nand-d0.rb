require 'arby/arby_dsl'
require 'arby/ast/bounds'
require 'arby_models/synth/synth2'

module ArbyModels::Synth
  extend Arby::Dsl

  alloy :ParityNandD0 do
    open Synth2

    # ---------
    # -- Vars
    # ---------

    one sig A, B, C, D < BoolVar
    one sig LitTrue, LitFalse < BoolLit

    fact bool_lit_vals {
      boolval == LitTrue**BitTrue + LitFalse**BitFalse
    }

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
    parity[a, b, c, d] = Not[And[eval[root],
                                 Not[And[Not[And[Not[And[d, Not[And[d, a]]]], 
                                                 Not[And[a, Not[And[d, a]]]]]], 
                                         Not[And[Not[And[Not[And[BitTrue, c]], 
                                                         Not[And[BitTrue, b]]]], 
                                                 Not[And[b, c]]]]]]]]
"""
    }

    run :synthBoolNode, 3, Int=>-1..0,  Nand => exactly(11), AndInv=>0, Not=>0, And=>0, 
                                   ITE=>0, IntVar=>0, IntLit=>0, Nor=>0, OrInv => 0,
                                   GT=>0, GTE=>0, LT=>0, LTE=>0, Equals=>0, Or=>0
  end
end
