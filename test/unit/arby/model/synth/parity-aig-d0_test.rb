require 'unit/arby/model/synth/parity_test_base'
require 'arby_models/synth/parity-aig-d0'

class SynthParityAigD0Test < SynthParityTestBase
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions
  include Arby::Bridge

  def setup_class
    Arby.reset
    Arby.meta.restrict_to(ArbyModels::Synth)
  end

  def setup_test
    @timer = SDGUtils::Timing::Timer.new
    @model = ArbyModels::Synth::ParityAigD0
  end

  def test0() do_test_synth @model, 0 end
  def test1() do_test_synth @model, 1 end

  def actual(aig_part, a, b, c, d)
    aig_part & (!(((!(a && b)) && (!(!a && !b))) && ((!(!c && !d)) && (!(c && d)))))
  end
end
