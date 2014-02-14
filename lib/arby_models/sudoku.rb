require 'arby/arby_dsl'
require 'arby/ast/bounds'

Arby.conf.sym_exe.convert_missing_fields_to_joins = true

module ArbyModels
  extend Arby::Dsl

  alloy_model :SudokuModel do
    self::N = 9

    sig Sudoku [
      grid: Int * Int * (lone Int)
    ] {
      # grid[Int][Int].in?(1..N) and
      # all(i: 0...N, j: 0...N) { one grid[i][j] } and
      grid[Int].Int.in?(0...N) and
      grid.Int.Int.in?(0...N)
    }

    pred solved[s: Sudoku] {
      all(r: 0..8) {
        s.grid[r][Int] == (1..9) and
        s.grid[Int][r] == (1..9)
      } and
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
      m = Integer(Math.sqrt(N))
      sq = Array(0...m).map{|i| (m*i)..(m*(i+1)-1)}
      sq_exprs = sq.product(sq).map{|r, c|
        s.grid[r][c] == (1..N)
      }
      rc_exprs = (0...N).map{|i|
        s.grid[i][Int] == (1..N) &&
        s.grid[Int][i] == (1..N)
      }

      conj(*rc_exprs, *sq_exprs)
    }

    pred solved3[s: Sudoku] {
      m = Integer(Math.sqrt(N))
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

  class SudokuModel::Sudoku
    def self.parse(str)
      rows = str.split("\n").map(&:strip).reject(&:empty?)
      fail "expected exactly #{N} lines, got #{rows.size}" unless rows.size == N
      fail "expected exactly #{N} chars in each line" unless rows.all?{|r| r.size == N}
      self.new :grid => rows.each_with_index.map{ |row, row_idx|
        row.chars.each_with_index.map{ |ch, col_idx|
          (ch>="1" && ch<=String(N)) ? [row_idx, col_idx, Integer(ch)] : nil
        }.compact
      }.flatten(1)
    end

    def self.parse2(str) Sudoku.new grid: 
      str.split(/\s*;\s*/).map{|x| x.split(/\s*,\s*/).map(&:to_i)}
    end

    def partial_instance
      bounds = Arby::Ast::Bounds.new
      indexes = (0...N) ** (0...N) - self.grid.project(0..1)
      bounds.bound(Sudoku.grid, self ** self.grid, self ** indexes ** (1..N))
      bounds.bound(Sudoku, self)
      bounds.bound_int(0..N)
      bounds
    end

    def solve
      SudokuModel.solve(:solved3, self.partial_instance)
    end

    def print
      m = Integer(Math.sqrt(N))
      dshs = "-"*(m*2+1)
      dsha = m.times.map{dshs}
      dshjp = dsha.join('+')
      "+#{dshjp}+\n" +
        (0...N).map{|i|
          row = (0...N).map{|j|
            s = self.grid[i][j]
            cell = s.empty?() ? "." : s.to_s
            j % m == 0 ? "| #{cell}" : cell
          }.join(" ") + " |"
        i > 0 && i % m == 0 ? "|#{dshjp}|\n#{row}" : row
        }.join("\n") + "\n" +
        "+#{dshjp}+"
    end
  end

end
