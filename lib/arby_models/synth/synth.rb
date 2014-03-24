require 'arby/arby_dsl'
require 'arby/ast/bounds'

module ArbyModels
module Synth
  extend Arby::Dsl

  alloy :Synth do

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
    abstract sig BoolCmp extends BoolNode [
      left, right: IntNode
    ]
    sig EQ, GT, GTE, LT, LTE < BoolCmp


    abstract sig Var extends IntNode
    abstract sig IntLit extends IntNode [ intval: (one Int) ]

    # --------------------------------------------------------------------------------
    # -- Semantics
    # --------------------------------------------------------------------------------
    pred iteSemantics[eval: Node.e ** (Int+Boolean)] {
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
      }
    }

    procedure cmpSemantics[cls: BoolCmp, op: Symbol, eval: Node.e ** (Int+Boolean)] {
      all(n: cls) {
        eval[n].in? Boolean and
        eval[n.left].in? Int and
        eval[n.right].in? Int and
        if eval[n.left].send(op, eval[n.right])
          eval[n] == BoolTrue
        else
          eval[n] == BoolFalse
        end
      }
    }

    pred gteSemantics[eval: Node.e ** (Int+Boolean)] { cmpSemantics(GTE, :>=, eval) }
    pred lteSemantics[eval: Node.e ** (Int+Boolean)] { cmpSemantics(LTE, :<=, eval) }
    pred gtSemantics[eval: Node.e ** (Int+Boolean)]  { cmpSemantics(GT,  :>,  eval) }
    pred ltSemantics[eval: Node.e ** (Int+Boolean)]  { cmpSemantics(LT,  :<,  eval) }
    pred eqSemantics[eval: Node.e ** (Int+Boolean)]  { cmpSemantics(EQ,  :==, eval) }

    pred varSemantics[eval: Node.e ** (Int+Boolean)] {
      all(v: Var) { one eval[v] and eval[v].in? Int }
    }

    pred intLitSemantics[eval: Node.e ** (Int+Boolean)] {
      all(i: IntLit) { eval[i] == i.intval }
    }

    pred semantics[eval: Node.e ** (Int+Boolean)] {
      iteSemantics[eval] and
      gteSemantics[eval] and
      lteSemantics[eval] and
      gtSemantics[eval] and
      ltSemantics[eval] and
      eqSemantics[eval] and
      varSemantics[eval] and
      intLitSemantics[eval]
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

    pred synth[root: IntNode] {
"""
  all env: Var -> one Int {
    some eval: Node -> one (Int+Boolean) |{
      env in eval
      semantics[eval]
    } |{
      spec[root, eval]
    }
  }
"""
    }
  end

  module Synth
    class Node;
      def to_oo()  self end
      def unwrap() self end
    end
    class BoolTrue;  def to_s() "true" end end
    class BoolFalse; def to_s() "false" end end
    class Var;       def prnt(i="") i + self.class.relative_name end end
    class IntLit;
      def prnt(i="")
        i + intval.to_s
      end
      def to_oo()
        self.intval = intval[0][0] if Array === intval
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
    class BoolCmp
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
        when EQ  then "=="
        end
      end
      def prnt(i="")
        "#{left.unwrap.prnt} #{op} #{right.unwrap.prnt}"
      end
    end

    def self.interpret(node, env)
      n = node.class == Arby::Ast::TupleSet ? node.unwrap : node
      case n
      when BoolTrue  then true
      when BoolFalse then false
      when IntLit    then n.intval
      when Var       then env[n]
      when BoolCmp
        interpret(n.left, env).send n.op, interpret(n.right, env)
      when ITE
        interpret(n.condition, env) ? interpret(n.then, env) : interpret(n.elsen, env)
      end
    end
  end
end
end
