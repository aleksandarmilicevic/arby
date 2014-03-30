require 'arby/arby_dsl'
require 'arby/ast/bounds'
require 'arby_models/synth/synth'

module ArbyModels::Synth
  extend Arby::Dsl

  def self.gen_array_search(n)
    alloy :"ArraySearch#{n}" do
      open Synth

      # ---------
      # -- Vars
      # ---------
      one sig LitI0 extends IntLit
      one sig VarK extends Var

      @@xs = []
      @@is = [LitI0]

      def self.xs() @@xs end
      def self.is() @@is end

      (1..n).each { |i|
        x = one sig VarX.(i) < Var
        i = one sig LitI.(i) < IntLit

        @@xs += x.return_result(:array)
        @@is += i.return_result(:array)
      }


      fact intLitVals {
        conj(self.__type.klass.is.map{|i|
          i.(intval) == Integer(i.relative_name[4..-1])
        })
      }


      # ---------
      # -- Spec
      # ---------

      pred spec[root: Node, eval: Node.e ** (Int + Boolean)] {
        xs = self.__type.klass.xs
        n = xs.size

        ord = conj((0...xs.size-1).map{|i| eval[xs[i]] < eval[xs[i+1]]})
        cs = []
        cs << ((eval[root] == 0 if eval[VarK] < eval[xs[0]]) if ord)
        cs << ((eval[root] == n if eval[VarK] > eval[xs[n-1]]) if ord)

        (1...xs.size).map{|i|
          cs << ((eval[root] == i if eval[VarK] > eval[xs[i-1]] and eval[VarK] < eval[xs[i]]) if ord)
        }
        conj(cs)
      }

      run :synth, 4*n+2, Int=>-1..(n+1), EQ=>0

      run :synth, 4*n+2, Int=>-1..(n+1), EQ=>0, GTE=>0, LTE=>0

      run :synth, 4*n+2, Int=>-1..(n+1), EQ=>0, GTE=>0, LTE=>0, GT=>0,
                         ITE=>exactly(n+1), LT=>exactly(n)

    end.return_result(:array).first
  end

end
