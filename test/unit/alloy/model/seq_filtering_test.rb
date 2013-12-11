require 'my_test_helper'
require 'arby_models/seq_filtering'

class SeqFilteringTest < Test::Unit::TestCase
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions

  include ArbyModels::SeqFiltering

  def setup_class
    Alloy.reset
    Alloy.meta.restrict_to(ArbyModels::SeqFiltering)
    Alloy.initializer.init_all_no_freeze

    @@als_model = ArbyModels::SeqFiltering.meta.to_als
  end

  def test1
    puts @@als_model
  end

end
