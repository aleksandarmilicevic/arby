require 'my_test_helper'
require 'arby/bridge/compiler'
require 'arby/bridge/solution'
require 'arby_models/seq_filtering'

class SeqFilteringTest < Test::Unit::TestCase
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions
  include Arby::Bridge

  include ArbyModels::SeqFiltering

  def setup_class
    Arby.reset
    Arby.meta.restrict_to(ArbyModels::SeqFiltering)
  end

  def test1
    als_model = ArbyModels::SeqFiltering.meta.to_als
    puts als_model
    puts "compiling..."
    compiler = Compiler.compile(als_model)
    puts "solving..."
    sol = compiler.execute_command(0)
    max_iter = 3 #10000000000000
    iter = 0
    while sol.satisfiable? do
      break if iter > max_iter
      iter += 1
      inst = sol.arby_instance()
      s = to_arr inst.skolem("$filter_s")
      ans = to_arr inst.skolem("$filter_ans")
      puts "checking #{pr s} -> #{pr ans}"
      check_filter(s, ans)
      sol = sol.next()
    end
  end

  def to_arr(ts)
    ts.map{|a| a[1]}
  end

  def check_filter(s, ans)
    expected = s.select{|a| a.x < 3}
    assert_seq_equal expected, ans
  end

  def pr(ts)
    ts.map{|a| "#{a.label}(#{a.x.first[0]})"}.inspect
  end

end
