require 'my_test_helper'
require 'arby/bridge/reporter'
require 'arby_models/synth/array_search'

class SynthArraySearchTest < Test::Unit::TestCase
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions
  include Arby::Bridge

  Synth = ArbyModels::Synth::Synth

  include Synth

  def setup_class
    Arby.reset
    Arby.meta.restrict_to(ArbyModels::Synth)
  end

  def test_als()
    m = ArbyModels::Synth.gen_array_search(4)
    puts! m.to_als
    assert m.compile
  end

  def test_search()
    begin
      puts! "reading N"; n = Integer(ENV["N"])
      puts! "reading C"; c = Integer(ENV["C"])
      puts! "reading F"; f = ["true", "yes"].member?(ENV["F"])
    rescue => e
      puts! "#{e}"
      return
    end
    do_test_search(n, c, f)
  end

  # def test_search2() do_test_search(2, 2) end
  def test_search3() do_test_search(3, 2) end
  # def test_search4() do_test_search(4, 2) end
  # def test_search5() do_test_search(5, 2) end

  def do_test_search(n, cmd_idx, full_inc=false)
    puts! "array_search_#{n} run_#{cmd_idx} #{full_inc ? 'FULL' : 'INC'}"
    # reporter: Rep.new
    Arby.conf.do_with(wrap_field_values: false) do
    Arby.conf.a4options.do_with(
        convertHolInst2A4Sol: false,
        holFullIncrements: full_inc,
        holMaxIter: 100) do
      model = ArbyModels::Synth.gen_array_search(n)
      # puts! model.to_als
      puts! "compiling/solving"
      sol = model.execute_command cmd_idx
      assert sol.sat?
      puts! "solving time: #{sol.solving_time}"
      puts! "num candidates: #{sol._a4sol.getStats().numCandidates()}"
      check_sol(sol)
    end
    end
  end

  def check_sol(sol)
    puts! "testing..."
    r = sol["$synth_root"].first.first
    r = r.to_oo
    puts! r.prnt
    vars = sol[Var]
    k = vars[0]
    xs = Hash[vars[1..-1].each_with_index.map{|x, i| [x, 20*(i+1)]}]
    (0..xs.size).each do |pos|
      env = xs.merge k => pos*20+1
      exp = pos
      res = Synth.interpret(r, env)
      puts! "test env: #{env}; expected: #{exp}; actual: #{res}"
      assert_equal exp, res
    end
  end

end


class Rep < Arby::Bridge::Reporter
  include Arby::Bridge
  def holLoopStart(tr, formula, bounds)
    puts "start"
  end
  def holCandidateFound(tr, candidate)
    puts "candidate found"
  end
  def holVerifyingCandidate(tr, candidate, checkFormula, bounds) end
  def holCandidateVerified(tr, candidate) end
  def holCandidateNotVerified(tr, candidate, cex) end
  def holFindingNextCandidate(tr, inc) end
end
