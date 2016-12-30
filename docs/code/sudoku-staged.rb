def dec(sudoku, order=Array(0...sudoku.grid.size).shuffle)
 return nil if order.empty? # all possibilities exhausted
 s_dec = Sudoku.new grid: sudoku.grid.delete_at(order.first) # delete a tuple at random position
 sol   = s_dec.clone.solve() # clone so that "s_dec" doesn't get updated if a solution is found
 (sol.satisfiable? && !sol.next.satisfiable?) ? s_dec : dec(sudoku, order[1..-1])
end
def min(sudoku) (s1 = dec(sudoku)) ? min(s1) : sudoku end
s = Sudoku.new; s.solve(); s = min(s); puts "local minimum found: #{s.grid.size}"
