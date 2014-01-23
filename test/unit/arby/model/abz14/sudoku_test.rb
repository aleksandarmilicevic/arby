require 'my_test_helper'
require 'arby_models/abz14/sudoku'

class ABZ14SudokuTest < Test::Unit::TestCase
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions
  include Arby::Bridge

  include ArbyModels::ABZ14::SudokuModel

  def setup_class
    Arby.reset
    Arby.meta.restrict_to(ArbyModels::ABZ14::SudokuModel)
    @@puzle = """
......95.
.8.7..6..
4...68...
3...5.7.2
...9.4...
2.6.1...5
...18...9
..2..3.6.
.35......
"""
    @@num_given = 26
  end

  def test_als
    puts ArbyModels::ABZ14::SudokuModel.meta.to_als
    assert ArbyModels::ABZ14::SudokuModel.compile
  end

  def do_test_n(n)
    old = ArbyModels::ABZ14::SudokuModel.N
    ArbyModels::ABZ14::SudokuModel.N = n

    puts "solving sudoku for size #{n}"
    s = Sudoku.new
    sol = ArbyModels::ABZ14::SudokuModel.solve :solved, s.partial_instance
    assert sol.satisfiable?, "instance not found"
    assert_equal n*n, s.grid.size
  ensure
    ArbyModels::ABZ14::SudokuModel.N = old
  end

  def test_size4()  do_test_n(4) end
  def test_size9()  do_test_n(9) end
  # def test_size16() do_test_n(16) end

  def test_abz
    old = ArbyModels::ABZ14::SudokuModel.N
    ArbyModels::ABZ14::SudokuModel.N = 4

    puts "solving sudoku for size #{4}"
    s = Sudoku.new :grid => [[0, 0, 1], [0, 3, 4], [3, 1, 1], [2, 2, 3]]
    puts s.print
    sol = ArbyModels::ABZ14::SudokuModel.solve :solved, s.partial_instance
    assert sol.satisfiable?, "instance not found"
    fail unless s.grid.size == 16
    assert_equal 16, s.grid.size
    puts s.print
    binding.pry
  ensure
    ArbyModels::ABZ14::SudokuModel.N = old
  end

  def test_instance_pi
    s = Sudoku.parse @@puzle
    puts s.print

    old_grid = s.grid.dup

    puts "solving sudoku with partial instance..."
    sol = ArbyModels::ABZ14::SudokuModel.solve :solved, s.partial_instance
    puts "solving time: #{sol.solving_time}s"

    assert sol.satisfiable?, "instance not found"
    assert_equal 81, s.grid.size
    assert old_grid.in?(s.grid)

    a4bounds = sol._a4sol.getBoundsSer
    a4sudoku_bounds = a4bounds.get("this/#{Sudoku.alloy_name}")
    a4grid_bounds = a4bounds.get("this/#{Sudoku.grid.full_alloy_name}")

    assert_equal 1, a4sudoku_bounds.a.size()
    assert_equal 1, a4sudoku_bounds.b.size()

    assert_equal 26, a4grid_bounds.a.size()
    assert_equal 521, a4grid_bounds.b.size()

    puts
    puts s.print
  end


end
