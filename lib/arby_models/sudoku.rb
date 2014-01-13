require 'arby/arby_dsl'
require 'arby/ast/bounds'

Arby.conf.sym_exe.convert_missing_fields_to_joins = true

module ArbyModels
  extend Arby::Dsl

  alloy_model :SudokuModel do
    self::N = 9

    sig Sudoku [
      grid: Int[0...N] * Int[0...N] * (lone Int[1..N])
    ] {
      # grid[Int][Int].in?(1..N) and
      grid[Int].Int.in?(0...N) and
      grid.Int.Int.in?(0...N) # and
      # all(i: 0...N, j: 0...N) { one grid[i][j] }
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
      sq = (0...m).map{|i| (m*i)..(m*(i+1)-1)}
      sq_exprs = sq.product(sq).map{|r, c|
        s.grid[r][c] == (1..N)
      }
      rc_exprs = (0...N).map{|i|
        s.grid[i][Int] == (1..N) &&
        s.grid[Int][i] == (1..N)
      }

      conj(*rc_exprs, *sq_exprs)
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

    def partial_instance
      bounds = Arby::Ast::Bounds.new
      bounds.add_lower(Sudoku.grid, self.to_ts ** self.grid)
      indexes = (0...N) ** (0...N) - self.grid.project(0..1)
      bounds.add_upper(Sudoku.grid, self.to_ts ** indexes ** (1..N))
      bounds.bound(Sudoku, self)
      bounds.bound_int(0..N)
      bounds
    end

    def print
      "+-------+-------+-------+\n" +
        (0..8).map{|i|
          row = (0..8).map{|j|
            s = self.grid[i][j]
            cell = s.empty?() ? "." : s.to_s
            j % 3 == 0 ? "| #{cell}" : cell
          }.join(" ") + " |"
          i > 0 && i % 3 == 0 ? "|-------+-------+-------|\n#{row}" : row
        }.join("\n") + "\n" +
      "+-------+-------+-------+"
    end
  end

end
