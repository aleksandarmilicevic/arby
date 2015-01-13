require 'my_test_helper'
require 'arby/bridge/reporter'
require 'arby_models/synth/max'

class SynthMaxTest < Test::Unit::TestCase
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions
  include Arby::Bridge

  Synth = ArbyModels::Synth::Synth

  include Synth

  def setup_class
    Arby.reset
    Arby.meta.restrict_to(ArbyModels::Synth)
  end

  def setup_test
    @timer = SDGUtils::Timing::Timer.new
  end

  def _test_als()
    m = ArbyModels::Synth.gen_max(3)
    puts! m.to_als
    assert m.compile
  end

  # def test_max3() do_test_max(3, 0) end
  # def test_max4() do_test_max(4, 0) end
  # def test_max5() do_test_max(5, 2) end
  # def test_max6() do_test_max(6, 0) end

  # def test_max3t() do_test_max(3, 1) end
  # def test_max4t() do_test_max(4, 1) end
  # def test_max5t() do_test_max(5, 1) end
  # def test_max6t() do_test_max(6, 1) end
  # def test_max7t() do_test_max(7, 1) end

  def _test_max()
    begin
      n = Integer(ENV["N"])
      c = Integer(ENV["C"])
      f = ["true", "yes"].member?(ENV["F"])
    rescue Exception => e
      return
    end
    do_test_max(n, c, f)
  end

  def test_max() do_test_max(4, 2, false) end

  def do_test_max(n, cmd_idx, full_inc=false)
    puts! "max#{n} run_#{cmd_idx} #{full_inc ? 'FULL' : 'INC'}"
    # reporter: Rep.new
    Arby.conf.do_with(wrap_field_values: false) do
    Arby.conf.a4options.do_with(
        solver: "MiniSatJNI",
        convertHolInst2A4Sol: false,
        holFullIncrements: full_inc,
        holMaxIter: 1000) do
      model = ArbyModels::Synth.gen_max(n)
      # puts! model.to_als
      puts! "compiling/solving"
      sol = model.execute_command cmd_idx
      assert sol.sat?
      puts! "solving time: #{sol.solving_time}"
      puts! "num candidates: #{sol._a4sol.getStats().numCandidates()}"
      # check_sol(sol)
    end
    end
  end

  def check_sol(sol)
    r = sol["$synth_root"].first.first
    r = r.to_oo
    puts! r.prnt
    vars = sol[Var]
    puts! "testing..."
    @timer.time_it {
      varvals = (1..vars.size).to_a
      inputs = (1...vars.size).reduce(varvals) {|acc, _| acc.product varvals}
      puts! "(num test inputs = #{inputs.size})"
      inputs.flatten.each_slice(vars.size) do |vals|
        env = (0...vals.size).reduce({}) {|acc, i| acc[vars[i]] = vals[i]; acc}
        exp = vals.max
        res = Synth.interpret(r, env)
        # puts! "test env: #{env}; expected: #{exp}; actual: #{res}"
        assert_equal exp, res
      end
    }
    puts! "testing time: #{@timer.last_time}"
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
