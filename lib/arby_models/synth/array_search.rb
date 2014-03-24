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
      one sig I0 extends IntLit
      one sig K extends Var

      @@xs = []
      @@is = [I0]

      def self.xs() @@xs end
      def self.is() @@is end

      (1..n).each { |i|
        x = one sig X.(i) < Var
        i = one sig I.(i) < IntLit

        @@xs += x.return_result(:array)
        @@is += i.return_result(:array)
      }


      fact intLitVals {
        conj(self.__type.klass.is.map{|i|
          i.(intval) == Integer(i.relative_name[1..-1])
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
        cs << ((eval[root] == 0 if eval[K] < eval[xs[0]]) if ord)
        cs << ((eval[root] == n if eval[K] > eval[xs[n-1]]) if ord)

        (1...xs.size).map{|i|
          cs << ((eval[root] == i if eval[K] > eval[xs[i-1]] and eval[K] < eval[xs[i]]) if ord)
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
