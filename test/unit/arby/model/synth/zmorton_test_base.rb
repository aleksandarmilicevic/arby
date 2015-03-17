require 'my_test_helper'
require 'arby/bridge/reporter'
require 'arby_models/synth/synth2'

class SynthZMortonTestBase < Test::Unit::TestCase
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
        holMaxIter:           100,
        noOverflow:           false,
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
    r = sol["$synthIntNodeI_root"].first.first
    r = r.to_oo()
    puts! r.prnt
    vars = sol[IntVar]
    varvals = (-8..7).to_a
    inputs = (1...vars.size).reduce(varvals) {|acc, _| acc.product varvals}
    inputs.flatten.each_slice(vars.size) do |vals|
      env =  (0...vals.size).reduce({}) {|acc, i| acc[vars[i]] = vals[i]; acc}
      i = vals[0]; j = vals[1]
      zmorton = (0x55555555 & ((0x33333333 & (((0x0000FFFF & j) << 0x00000002) | 
                                              (0x0000FFFF & j))) | 
                               ((0x33333333 & (((0x0000FFFF & j) << 0x00000002) | 
                                               (0x0000FFFF & j))) << 0x00000001))) | 
                ((0x55555555 & (((0x33333333 & (((0x0000FFFF & i) << 0x00000002) | 
                                                (0x0000FFFF & i))) << 0x00000001) | 
                                (0x33333333 & (((0x0000FFFF & i) << 0x00000002) | 
                                               (0x0000FFFF & i))))) << 0x00000001)
      puts! "testing: zmorton#{vals} = #{zmorton}"
      ans_part = Synth.interpret(r, env)
      ans_full = actual(ans_part, i, j)
      binding.pry unless zmorton == ans_full
      assert_equal zmorton, ans_full
    end
  end
end
