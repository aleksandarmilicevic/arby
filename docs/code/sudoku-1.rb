alloy :SudokuModel do
 SudokuModel::N = 9

 sig Sudoku[grid: Int ** Int ** (lone Int)]

 pred solved[s: Sudoku] {
  m   = Integer(Math.sqrt(N))
  rng = lambda{|i| m*i...m*(i+1)}

  all(r: 0...N) { 
   s.grid[r][Int] == (1..N) and 
   s.grid[Int][r] == (1..N) 
  } and
  all(c, r: 0...m) { 
   s.grid[rng[c]][rng[r]] == (1..N) 
  }
 }
end
