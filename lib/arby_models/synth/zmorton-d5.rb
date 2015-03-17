require 'arby/arby_dsl'
require 'arby/ast/bounds'
require 'arby_models/synth/synth2'

module ArbyModels::Synth
  extend Arby::Dsl

  alloy :ZMortonD5 do
    open Synth2

    # ---------
    # -- Vars
    # ---------

    one sig I, J < IntVar
    one sig Hex1, Hex2, HexFFFF, Hex33333333, Hex55555555 < IntLit

    fact intLitVals {
      IntLit.<(intval) == Hex1**1 + Hex2**2 + HexFFFF**0xFFFF + Hex33333333**0x33333333 + Hex55555555**0x55555555
    }

    # ---------
    # -- Spec
    # ---------
    fun zmorton_spec[i, j: Int][Int] {
"""
bvor[bvand[0x55555555, bvor[bvand[0x33333333, bvor[bvshl[bvand[0xFFFF, j], 2], bvand[0xFFFF, j]]], 
                              bvshl[bvand[0x33333333, bvor[bvshl[bvand[0xFFFF, j], 2], bvand[0xFFFF, j]]], 1]]], 
     bvshl[bvand[0x55555555, bvor[bvshl[bvand[0x33333333, bvor[bvshl[bvand[0xFFFF, i], 2], bvand[0xFFFF, i]]], 1],
                                    bvand[0x33333333, bvor[bvshl[bvand[0xFFFF, i], 2], bvand[0xFFFF, i]]]]], 1]]
"""
    }

    pred spec[root: Node, eval: Node.e ** (Int + Bit)] {
"""
  let i = eval[I], j = eval[J] |
    zmorton_spec[i, j] = eval[root]
"""
    }

    run :synthIntNodeI, 0, Int=>{bitwidth: 32, atoms: [literals, bw(4)]},  
                                   BvAnd=>exactly(14), BvOr=>exactly(7), BvShl=>exactly(7)
  end
end
