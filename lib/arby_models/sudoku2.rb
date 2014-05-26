require 'arby/arby_dsl'
require 'arby/ast/bounds'

module ArbyModels
  extend Arby::Dsl

  def self.gen_sudoku(n)
    m = Math.sqrt(n).to_i
    ans = alloy "Sudoku#{n}" do
      abstract sig Digit
       sig Cell [
        content: (one Digit)
      ] 

      sig Group [
        cells: (set Cell)
      ] {
        no(c1, c2: cells) { c1 != c2 and c1.content == c2.content }
      }

      (0...n).each do |i|
        one sig "D#{i}" < Digit 
        one sig "R#{i}", "C#{i}", "M#{i}" < Group
        (0...n).each{ |j| one sig "C#{i}#{j}" < Cell }
      end

      (0...n).each do |i|
        # row cells
        row_sig = meta["R#{i}"]
        row_cell_sigs = (0...n).map{|j| meta["C#{i}#{j}"]}
        fact { row_sig.(cells) == union(row_cell_sigs) }

        # col cells
        col_sig = meta.find_sig("C#{i}")
        col_cell_sigs = (0...n).map{|j| meta["C#{j}#{i}"]}
        fact { col_sig.(cells) == union(col_cell_sigs) }

        # matrix cells
        x, y = i.divmod(m).map(&:to_i)
        mat_cell_sigs = ((0...m)**(0...m)).map{|i,j| meta["C#{x*m+i}#{y*m+j}"]}
        fact { meta["M#{i}"].(cells) == union(mat_cell_sigs) }
      end
    end  
    ans.return_result(:array).first
  end
end
