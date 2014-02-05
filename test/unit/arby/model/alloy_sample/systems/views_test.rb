require 'my_test_helper'
require 'arby/helpers/test/dsl_helpers'

require 'arby_models/alloy_sample/systems/views'

class ViewsTest < Test::Unit::TestCase
  include Arby::Helpers::Test::DslHelpers
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions
  include Arby::Bridge

  Views = ArbyModels::AlloySample::Systems::Views
  include Views

  def setup_class
    Arby.reset
    Arby.meta.restrict_to(Views)
  end

  def test_als
    puts Views.meta.to_als
    assert Views.compile
  end

end
