require 'unit/arby/model/synth/parity_test_base'
require 'arby_models/synth/parity-nand-d0'

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
    @model = ArbyModels::Synth::ParityNandD0
  end

  def test0()
    do_test_synth @model, 0
  end

  def actual(aig_part, a, b, c, d)
      !(aig_part &&
        !(!(!(d && !(d && a)) && !(a && !(d && a))) && !(!(!(true && c) && !(true && b)) && !(b && c))))
  end

end
