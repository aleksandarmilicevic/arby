require 'my_test_helper'
require 'arby_models/sudoku'
require 'arby/helpers/test/dsl_helpers'
require 'sdg_utils/timing/timer'

class SudokuTestBase < Test::Unit::TestCase
  include Arby::Helpers::Test::DslHelpers
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions

  SudokuModel = ArbyModels::SudokuModel
  include SudokuModel

  def setup_class
    Arby.reset
    Arby.meta.restrict_to(SudokuModel)

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
    @@timer = SDGUtils::Timing::Timer.new
  end

  def with_N(n)
    old = SudokuModel.N
    SudokuModel.N = n
    yield
  ensure
    SudokuModel.N = old
  end

  def do_test_n(n)
    with_N(n) do
      puts "solving sudoku for size #{n}"
      s = Sudoku.new
      sol = s.solve()
      assert sol.satisfiable?, "instance not found"
      assert_equal n*n, s.grid.size
    end
  end

  def gen(n_filled=SudokuModel.N * SudokuModel.N)
    s = Sudoku.new
    sol = s.solve
    return nil unless sol.satisfiable?
    while s && s.grid.size > n_filled do fail(); s = dec(s); end
    s
  end

  def dec(sudoku, order=Array(0...sudoku.grid.size).shuffle)
    return nil if order.empty?
    s1 = Sudoku.new :grid => sudoku.grid.delete_at(order.first)
    sol = s1.clone.solve()
    (sol.satisfiable? && !sol.next.satisfiable?) ? s1 : dec(sudoku, order[1..-1])
  end

  def min(sudoku)
    puts "minimizing size #{sudoku.grid.size}"
    (s1 = dec(sudoku)) ? min(s1) : sudoku
  end


  def test_als
    # puts SudokuModel.meta.to_als
    assert SudokuModel.compile
  end

  def test_instance
    return unless @pred
    puts "solving sudoku using pred #{@pred} ..."
    sol = SudokuModel.solve @pred, "for 1 but 5 Int"
    puts "solving time: #{sol.solving_time}s"

    assert sol.satisfiable?, "instance not found"
    # puts
    # @@timer.time_it { puts sol.arby_instance.atoms.first.print }
    # puts "print time: #{@@timer.last_time}"
  end

  def test_pi
    return if @pred
    s = Sudoku.parse @@puzle
    bounds = s.partial_instance
    assert_equal @@num_given, bounds.get_lower(Sudoku.grid).size
    assert_equal (81-@@num_given)*9 + @@num_given, bounds.get_upper(Sudoku.grid).size
    assert_equal 1, bounds.get_lower(Sudoku).size
    assert_equal 1, bounds.get_upper(Sudoku).size
    assert_equal 10, bounds.get_ints.size
  end

  def test_instance_pi
    return unless @pred
    s = Sudoku.parse @@puzle

    # puts
    # @@timer.time_it { puts s.print }
    # puts "print time: #{@@timer.last_time}"

    old_grid = s.grid

    puts "solving sudoku with partial instance using pred #{@pred}..."
    sol = SudokuModel.solve @pred, s.partial_instance, 1, Int => 5
    puts "solving time: #{sol.solving_time}s"

    assert sol.satisfiable?, "instance not found"
    assert_equal 81, s.grid.size
    assert old_grid.in?(s.grid)

    a4bounds = sol._a4sol.getBoundsSer
    # a4sudoku_bounds = a4bounds.get("this/#{Sudoku.alloy_name}")
    a4grid_bounds = a4bounds.get("this/#{Sudoku.grid.full_alloy_name}")

    # assert_equal 1, a4sudoku_bounds.a.size()
    # assert_equal 1, a4sudoku_bounds.b.size()

    assert_equal 26, a4grid_bounds.a.size()
    assert_equal 521, a4grid_bounds.b.size()

    # puts
    # @@timer.time_it { puts s.print }
    # puts "print time: #{@@timer.last_time}"
  end
end


class Sudoku1Test < SudokuTestBase; def setup_test() @pred = :solved end; end
class Sudoku2Test < SudokuTestBase; def setup_test() @pred = :solved2 end; end
class Sudoku3Test < SudokuTestBase; def setup_test() @pred = :solved3 end; end
class Sudoku4Test < SudokuTestBase
  def test_min
    with_N(4) do
      timer = SDGUtils::Timing::Timer.new
      s = timer.time_it {min(gen())}
      assert s
      puts! "local minimum found: #{s.grid.size}"
      puts! "total time: #{timer.last_time}"
    end
  end

  def test_parse2
    with_N(4) do
      s = Sudoku.parse2 "0,0,1; 0,3,4; 3,1,1; 2,2,3"
      s.solve();
      assert_equal 16, s.grid.size
      puts s.print
    end
  end

  def test_abz
    with_N(4) do
      puts "solving sudoku for size #{4}"
      s = Sudoku.new :grid => [[0, 0, 1], [0, 3, 4], [3, 1, 1], [2, 2, 3]]
      puts s.print
      sol = s.solve()
      assert sol.satisfiable?, "instance not found"
      fail unless s.grid.size == 16
      assert_equal 16, s.grid.size
      puts s.print
    end
  end

  def test_size4()  do_test_n(4) end
  def test_size9()  do_test_n(9) end
  # def test_size16() do_test_n(16) end
end
