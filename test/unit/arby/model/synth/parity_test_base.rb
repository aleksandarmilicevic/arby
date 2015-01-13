require 'my_test_helper'
require 'arby/bridge/reporter'
require 'arby_models/synth/synth2'

class SynthParityTestBase < Test::Unit::TestCase
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions
  include Arby::Bridge

  Synth = ArbyModels::Synth::Synth2

  include Synth

  def setup_class
    Arby.reset
    Arby.meta.restrict_to(ArbyModels::Synth)
  end

  def setup_test
    @timer = SDGUtils::Timing::Timer.new
  end

  def _test_als(model)
    puts! model.to_als
    assert m.compile
  end

  def do_test_synth(model, cmd_idx)
    Arby.conf.do_with(wrap_field_values: false) do
    Arby.conf.a4options.do_with(
        solver:               "MiniSatJNI",
        convertHolInst2A4Sol: false,
        holFullIncrements:    false,
        holMaxIter:           100
    ) do
      #puts! model.to_als
      puts! "compiling/solving"
      sol = model.execute_command cmd_idx
      puts! "solving time: #{sol.solving_time}"
      puts! "num candidates: #{sol._a4sol.getStats().numCandidates()}"
      assert sol.sat?
      check_sol(sol)
    end
    end
  end

  def check_sol(sol)
    puts! "testing..."
    r = sol["$synthBoolNode_root"].first.first
    r = r.to_oo()
    puts! r.prnt
    vars = sol[BoolVar]
    varvals = [false, true]
    inputs = (1...vars.size).reduce(varvals) {|acc, _| acc.product varvals}
    inputs.flatten.each_slice(vars.size) do |vals|
      env = (0...vals.size).reduce({}) {|acc, i| acc[vars[i]] = vals[i]; acc}
      a = vals[0]; b = vals[1]; c = vals[2]; d = vals[3]
      parity = !(a ^ b) ^ !(c ^ d)
      puts! "testing: parity#{vals} = #{parity}"
      aig_part = Synth.interpret(r, env)
      aig_full = actual(aig_part, a, b, c, d)
      binding.pry unless parity == aig_full
      assert_equal parity, aig_full
    end
  end
end
