require 'my_test_helper'
require 'alloy/bridge/compiler'
require 'alloy/bridge/solution'
require 'arby_models/seq_filtering'

class SeqFilteringTest < Test::Unit::TestCase
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions
  include Alloy::Bridge

  include ArbyModels::SeqFiltering

  def setup_class
    Alloy.reset
    Alloy.meta.restrict_to(ArbyModels::SeqFiltering)
    Alloy.initializer.init_all_no_freeze
  end


  def test1
    als_model = ArbyModels::SeqFiltering.meta.to_als
    puts als_model
    puts "compiling..."
    compiler = Compiler.compile(als_model)
    puts "solving..."
    sol = compiler.execute_command(0)
    while sol.satisfiable? do
      inst = sol.translate_to_arby
      s = to_arr inst.skolem("$filter_s")
      ans = to_arr inst.skolem("$filter_ans")
      puts "checking #{pr s} -> #{pr ans}"
      check_filter(s, ans)
      puts "finding next"
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
