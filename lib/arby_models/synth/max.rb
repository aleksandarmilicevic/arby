require 'arby/arby_dsl'
require 'arby/ast/bounds'
require 'arby_models/synth/synth'

module ArbyModels::Synth
  extend Arby::Dsl

  def self.gen_max(n)
    alloy :"Max#{n}" do
      open Synth

      # ---------
      # -- Vars
      # ---------

      (1..n).map { |i|
        one sig "X#{i}" < Var
      }

      # ---------
      # -- Spec
      # ---------

      pred spec[root: Node, eval: Node.e ** (Int + Boolean)] {
        vars = self.__type.klass.meta.sigs
        d = disj(vars.map{|v| eval[root] == eval[v]})
        c = conj(vars.map{|v| eval[root] >= eval[v]})
        c and d
      }

      run :synth, 3*(n-1) + 1, Int=>0..(n-1), LT=>0, GT=>0, IntLit=>0

      run :synth, 3*(n-1) + 1, Int=>0..(n-1), LT=>0, GT=>0, IntLit=>0,
                               LTE=>0, EQ=>0

      run :synth, 3*(n-1) + 1, Int=>0..(n-1), LT=>0, GT=>0, IntLit=>0,
                               LTE=>0, EQ=>0,
                               ITE => exactly(n-1), GTE => exactly(n-1)
    end.return_result(:array).first
  end

end
