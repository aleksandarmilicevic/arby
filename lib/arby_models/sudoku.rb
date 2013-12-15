require 'arby/arby_dsl'

module ArbyModels
  extend Arby::Dsl

  alloy_model :SudokuModel do
    sig Sudoku [
      grid: Int[0..8] * Int[0..8] * Int[1..9]
    ]

    pred solved[s: Sudoku] {
      s.grid[0..8][Int] == (1..9) and
      s.grid[Int][0..8] == (1..9) and
      s.grid[0..2][0..2] == (1..9) and
      s.grid[0..2][3..5] == (1..9) and
      s.grid[0..2][6..8] == (1..9) and
      s.grid[3..5][0..2] == (1..9) and
      s.grid[3..5][3..5] == (1..9) and
      s.grid[3..5][6..8] == (1..9) and
      s.grid[6..8][0..2] == (1..9) and
      s.grid[6..8][3..5] == (1..9) and
      s.grid[6..8][6..8] == (1..9)
    }

    pred solved2[s: Sudoku] {
      sq = [(0..2), (3..5), (6..8)]
      exprs = sq.product(sq).map{|r, c| s.grid[r][c] == (1..9)}

      s.grid[0..8][Int] == (1..9) and
      s.grid[Int][0..8] == (1..9) and
      conj(*exprs)
    }
  end


end
