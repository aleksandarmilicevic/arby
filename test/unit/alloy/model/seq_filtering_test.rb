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


  def _test1
    als_model = ArbyModels::SeqFiltering.meta.to_als
    puts als_model
    puts "compiling..."
    compiler = Compiler.compile(als_model)
    puts "solving..."
    sol = compiler.execute_command(0)
    while sol.satisfiable? do
      inst = sol.translate_to_arby
      pr inst.skolem("$filter_s")
      pr inst.skolem("$filter_ans")
      puts "finding next"
      sol = sol.next()
    end
  end

  def pr(ts)
    a = ts.map{|a| "#{a[1].label}(#{a[1].x[0][0]})"}
    puts a.inspect
  end

end
