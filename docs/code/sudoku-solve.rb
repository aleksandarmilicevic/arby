class SudokuModel::Sudoku
 def pi
  bnds = Arby::Ast::Bounds.new
  inds = (0...N)**(0...N) - self.grid.project(0..1)
  bnds[Sudoku]         = self
  bnds.lo[Sudoku.grid] = self ** self.grid
  bnds.hi[Sudoku.grid] = self ** inds ** (1..N)
  bnds.bound_int(0..N)
 end
 def solve() SudokuModel.solve :solved, self.pi end
 def display() puts grid end
 def self.parse(s) Sudoku.new grid: 
   s.split(/;\s*/).map{|x| x.split(/,/).map(&:to_i)}
 end
end
SudokuModel.N = 4
s = Sudoku.parse "0,0,1; 0,3,4; 3,1,1; 2,2,3"
s.solve(); s.display(); # => {<0,0,1>, <0,1,3>, ...}
