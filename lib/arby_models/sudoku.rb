require 'arby/arby_dsl'

Arby.conf.sym_exe.convert_missing_fields_to_joins = true

module ArbyModels
  extend Arby::Dsl

  alloy_model :SudokuModel do
    N = 9

    one sig Sudoku [
      grid: Int[0..8] * Int[0..8] * Int[1..9]
    ] {
      grid[Int][Int].in?(1..9) and
      grid[Int].Int.in?(0..8) and
      grid.Int.Int.in?(0..8) and
      all(i: 0..8, j: 0..8) { one grid[i][j] }
    }

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

    def to_s
      (0..8).map{ |i|
        (0..8).map{|j| s = self.grid[i][j]; (s.empty?) ? "." : s.to_s}.join(" ")
      }.join("\n")
    end
  end

end
