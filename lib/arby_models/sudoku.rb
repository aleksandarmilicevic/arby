require 'alloy/alloy_dsl'

module ArbyModels
  extend Alloy::Dsl

  alloy_model :SudokuModel do
    sig Sudoku [
      grid: Int[0..8] * Int[0..8] * Int[0..9]
    ] 

    pred solved[s: Sudoku] {
      s.grid[0..8][Int] == (1..9) and
      s.grid[Int][0..8] == (1..9)
    }
  end


end
