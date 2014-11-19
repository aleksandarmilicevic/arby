require 'my_test_helper'
require 'arby_models/stela/orm'
require 'sdg_utils/timing/timer'

class ORMTest < Test::Unit::TestCase
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions
  include Arby::Bridge

  include ArbyModels::Stela
  include ArbyModels::Stela::ORM

  def setup_class
    Arby.reset
    Arby.meta.restrict_to(ArbyModels::Stela)
    @@timer = SDGUtils::Timing::Timer.new
  end

  def test_als
    assert ORM.compile
  end

end
