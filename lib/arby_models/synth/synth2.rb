require 'arby/arby_dsl'
require 'arby/ast/bounds'

module ArbyModels
module Synth
  extend Arby::Dsl

  alloy :Synth2 do

    ::BitTrue = -1
    ::BitFalse = 0

    # --------------------------------------------------------------------------------
    # -- AST Nodes
    # --------------------------------------------------------------------------------
    abstract sig Node
    abstract sig IntNode extends Node
    abstract sig BoolNode extends Node

    # --------------------------------------------------------------------------------
    # -- BoolNodes
    # --------------------------------------------------------------------------------
    abstract sig IntCmp extends BoolNode [
      left, right: (one IntNode)
    ]
    abstract sig BoolCmp extends BoolNode [
      left, right: (one BoolNode)
    ]
    abstract sig BoolInvCmp extends BoolCmp [
      invLhs, invRhs, invOut: (one Bit)
    ]

    abstract sig BoolVar extends BoolNode
    abstract sig BoolLit extends BoolNode [ boolval: (one Bit) ]

    sig Equals, GT, GTE, LT, LTE < IntCmp
    sig And, Nand, Or, Nor, Xor < BoolCmp
    sig AndInv, OrInv < BoolInvCmp
    sig Not extends BoolNode [
      arg: (one BoolNode)
    ]

    # --------------------------------------------------------------------------------
    # -- IntNodes
    # --------------------------------------------------------------------------------

    abstract sig IntVar extends IntNode
    abstract sig IntLit extends IntNode [ intval: (one Int) ]
    abstract sig BinaryIntOp extends IntNode [
      left, right: (one IntNode)
    ] 
    abstract sig UnaryIntOp extends IntNode [
      arg: (one IntNode)
    ]

    sig ITE extends IntNode [
      condition: (one BoolNode),
      then:      (one IntNode),
      elsen:     (one IntNode)
    ]
    sig BvAnd, BvOr, BvXor, BvShl, BvShr, BvSha < BinaryIntOp
    sig BvNot < UnaryIntOp

    # --------------------------------------------------------------------------------
    # -- Semantics
    # --------------------------------------------------------------------------------
    procedure cmpSemantics[cls: IntCmp, op: Symbol, eval: Node.e ** (Int+Bit)] {
      all(n: cls) {
        if eval[n.left].send(op, eval[n.right])
          eval[n] == BitTrue
        else
          eval[n] == BitFalse
        end
      }
    }

    procedure ucmpSemantics[cls: BoolCmp, op: Symbol, eval: Node.e ** (Int+Bit)] {
      all(n: cls) { eval[n] == eval[n.arg].send(op) }
    }

    procedure bcmpSemantics[cls: BoolCmp, op: Symbol, eval: Node.e ** (Int+Bit)] {
      all(n: cls) { eval[n] == eval[n.left].send(op, eval[n.right]) }
    }

    procedure binvcmpSemantics[cls: BoolCmp, op: Symbol, eval: Node.e ** (Int+Bit)] {
      all(n: cls) {
        eval[n] == eval[n.left].Xor(n.invLhs).send(op, eval[n.right].Xor(n.invRhs)).Xor(n.invOut)
      }
    }

    pred semantics[eval: Node.e ** (Int+Bit)] {
      all(bnode: BoolNode) { one(eval[bnode]) && eval[bnode].in?(Bit) } and
      all(inode: IntNode)  { one(eval[inode]) && eval[inode].in?(Int) } and
      all(n: ITE) {
        if eval[n.condition] == BitTrue
          eval[n.then] == eval[n]
        else
          eval[n.elsen] == eval[n]
        end
      } and
      cmpSemantics(GTE, :>=, eval) and
      cmpSemantics(LTE, :<=, eval) and
      cmpSemantics(GT,  :>,  eval) and
      cmpSemantics(LT,  :<,  eval) and
      cmpSemantics(Equals,  :==, eval) and
      bcmpSemantics(And,  :And,  eval) and
      bcmpSemantics(Nand, :Nand, eval) and
      bcmpSemantics(Or,   :Or,   eval) and
      bcmpSemantics(Nor,  :Nor,  eval) and
      bcmpSemantics(Xor,  :Xor,  eval) and
      binvcmpSemantics(AndInv, :And,  eval) and
      binvcmpSemantics(OrInv, :Or,  eval) and
      ucmpSemantics(Not,   :Not, eval) and
      bcmpSemantics(BvAnd, :bvand, eval) and
      bcmpSemantics(BvOr,  :bvor, eval) and
      bcmpSemantics(BvXor, :bvxor, eval) and
      bcmpSemantics(BvShl, :bvshl, eval) and
      bcmpSemantics(BvShr, :bvshr, eval) and
      bcmpSemantics(BvSha, :bvsha, eval) and
      ucmpSemantics(BvNot, :bvnot, eval) and
      all(i: IntLit) { eval[i] == i.intval } and
      all(i: BoolLit) { eval[i] == i.boolval }
    }

    # --------------------------------------------------------------------------------
    # -- Property
    # --------------------------------------------------------------------------------
    pred irreflexive[r: univ ** univ] { no (iden & r) }

    pred acyclic[r: univ ** univ, s: (set univ)] {
      all(x: s) { not x.in?(x.^r) }
    }

    procedure bin_rels {
      condition + ITE.then + elsen + 
        Not.<(arg) + UnaryIntOp.<(arg) +
        IntCmp.<(left) + BoolCmp.<(left) + BinaryIntOp.<(left) +
        IntCmp.<(right) + BoolCmp.<(right) + BinaryIntOp.<(right)
    }

    fact {
      acyclic(bin_rels(), Node)
    }

    pred allVarsReachableFrom[root: Node] {
      all(v: BoolVar+IntVar) {
        v.in?(root.^(bin_rels()))
      }
    }

    pred synth[root: Node] {
"""
  allVarsReachableFrom[root]
  all envI: IntVar -> one Int {
  all envB: BoolVar -> one Bit {
    some eval: IntNode->Int + BoolNode->Bit |{
      envI in eval
      envB in eval
      semantics[eval]
    } |{
      spec[root, eval]
    }
  }
  }
"""
    }

    pred synthI[root: Node] {
"""
  allVarsReachableFrom[root]
  all envI: IntVar -> one Int {
    some eval: IntNode->Int + BoolNode->Bit |{
      envI in eval
      semantics[eval]
    } |{
      spec[root, eval]
    }
  }
"""
    }

    pred synthBoolNode[root: BoolNode] { synth[root] }
    pred synthIntNode[root: IntNode]   { synth[root] }
    pred synthIntNodeI[root: IntNode]  { synthI[root] }
  end

  module Synth2
    class Node;
      def to_oo()  self end
      def unwrap() self end
      def prnt(i="") i + self.class.relative_name end
    end
    class IntLit;
      def prnt(i="")
        i + intval.to_s
      end
      def to_oo()
        self.intval = intval[0][0] if Array === intval
        self
      end
    end
    class BoolLit;
      def prnt(i="")
        i + boolval.to_s
      end
      def to_oo()
        self.boolval = boolval[0][0] != 0 if Array === boolval
        self
      end
    end
    class ITE
      def to_oo()
        self.condition = condition[0][0].to_oo if Array === condition
        self.then      = self.then[0][0].to_oo if Array === self.then
        self.elsen     = self.elsen[0][0].to_oo if Array === self.elsen
        self
      end
      def prnt(i="")
        "#{i}if (#{condition.unwrap.prnt}) then {\n" +
        "#{i}#{self.then.unwrap.prnt(i + '  ')}\n" +
        "#{i}} else {\n" +
        "#{i}#{self.elsen.unwrap.prnt(i + '  ')}\n" +
        "#{i}}"
      end
    end
    class Not
      def to_oo()
        self.arg  = self.arg[0][0].to_oo if Array === self.arg
        self
      end
      def op()
        "!"
      end
      def prnt(i="")
        "(#{self.class.relative_name} #{arg.unwrap.prnt})"
      end
    end
    class BoolCmp
      def to_oo()
        self.left  = self.left[0][0].to_oo if Array === self.left
        self.right = self.right[0][0].to_oo if Array === self.right
        self
      end
      def op()
        case self
        when And  then "&"
        when Nand then "&!"
        when Or   then "|"
        when Nor  then "|!"
        when Xor  then "^"
        end
      end
      def prnt(i="")
        "(#{self.class.relative_name} #{left.unwrap.prnt} #{right.unwrap.prnt})"
      end
    end
    class BoolInvCmp
      def to_oo()
        super
        self.invLhs  = self.invLhs[0][0] != 0 if Array === self.invLhs
        self.invRhs  = self.invRhs[0][0] != 0 if Array === self.invRhs
        self.invOut  = self.invOut[0][0] != 0 if Array === self.invOut
        self
      end
      def op()
        lBang = invLhs ? '!' : ''
        rBang = invRhs ? '!' : ''
        oBang = invOut ? '!' : ''
        case self
        when AndInv then "#{lBang}#{rBang}&#{oBang}"
        when OrInv  then "#{lBang}#{rBang}|#{oBang}"
        end
      end
      def prnt(i="")
        lBang = invLhs ? '!' : ''
        rBang = invRhs ? '!' : ''
        oBang = invOut ? '!' : ''
        "#{i}(#{oBang}#{self.class.relative_name} #{lBang}#{left.unwrap.prnt} #{rBang}#{right.unwrap.prnt})"
      end
    end
    class BinaryIntOp
      def to_oo()
        self.left  = self.left[0][0].to_oo if Array === self.left
        self.right = self.right[0][0].to_oo if Array === self.right
        self
      end
      def op()
        self.class.relative_name()
      end
      def prnt(i="")
        "(#{self.class.relative_name} #{left.unwrap.prnt} #{right.unwrap.prnt})"        
      end
    end
    class IntCmp
      def to_oo()
        self.left  = self.left[0][0].to_oo if Array === self.left
        self.right = self.right[0][0].to_oo if Array === self.right
        self
      end
      def op()
        case self
        when GTE then ">="
        when GT  then ">"
        when LT  then "<"
        when LTE then "<="
        when Equals  then "=="
        end
      end
      def prnt(i="")
        "#{left.unwrap.prnt} #{op} #{right.unwrap.prnt}"
      end
    end

    def self.interpret(node, env)
      n = node.class == Arby::Ast::TupleSet ? node.unwrap : node
      case n
      when BitTrue  then true
      when BitFalse then false
      when IntLit   then n.intval
      when BoolLit  then n.boolval
      when IntVar   then env[n]
      when BoolVar  then env[n]
      when IntCmp
        interpret(n.left, env).send n.op, interpret(n.right, env)
      when ITE
        interpret(n.condition, env) ? interpret(n.then, env) : interpret(n.elsen, env)
      when And
        (!!interpret(n.left, env)) && (!!interpret(n.right, env))
      when Nand
        !((!!interpret(n.left, env)) && (!!interpret(n.right, env)))
      when Or
        (!!interpret(n.left, env)) || (!!interpret(n.right, env))
      when Nor
        !((!!interpret(n.left, env)) || (!!interpret(n.right, env)))
      when Xor
        (!!interpret(n.left, env)) ^ (!!interpret(n.right, env))
      when Not
        !interpret(n.arg, env)
      when BvAnd then interpret(n.left, env) & interpret(n.right, env) 
      when BvOr  then interpret(n.left, env) | interpret(n.right, env) 
      when BvXor then interpret(n.left, env) ^ interpret(n.right, env) 
      when BvShl then interpret(n.left, env) << interpret(n.right, env) 
      when BvShr then interpret(n.left, env) >> interpret(n.right, env) 
      when BvSha then raise "No SHA in ruby?"
      when AndInv
        lhs = !!interpret(n.left, env)
        lhs = !lhs if n.invLhs
        rhs = !!interpret(n.right, env)
        rhs = !rhs if n.invRhs
        out = lhs && rhs
        n.invOut ? !out : out
      when OrInv
        lhs = !!interpret(n.left, env)
        lhs = !lhs if n.invLhs
        rhs = !!interpret(n.right, env)
        rhs = !rhs if n.invRhs
        out = lhs || rhs
        n.invOut ? !out : out
      end
    end
  end
end
end
