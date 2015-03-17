require 'unit/arby/model/synth/zmorton_test_base'
require 'arby_models/synth/zmorton-d5'

class SynthParityAigD1Test < SynthZMortonTestBase
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions
  include Arby::Bridge

  def setup_class
    Arby.reset
    Arby.meta.restrict_to(ArbyModels::Synth)
  end

  def setup_test
    @timer = SDGUtils::Timing::Timer.new
    @model = ArbyModels::Synth::ZMortonD5
  end

  def test0() do_test_synth @model, 0 end

  def actual(zmorton_part, i, j)
      zmorton_part
  end

end
