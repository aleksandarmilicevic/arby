require 'my_test_helper'
require 'arby/helpers/test/dsl_helpers'

require 'arby_models/alloy_sample/toys/ceilingsAndFloors'

class CeilingsAndFloorsTest < Test::Unit::TestCase
  include Arby::Helpers::Test::DslHelpers
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions
  include Arby::Bridge

  CeilingsAndFloors = ArbyModels::AlloySample::Toys::CeilingsAndFloors
  include CeilingsAndFloors

  def setup_class
    Arby.reset
    Arby.meta.restrict_to(CeilingsAndFloors)
  end

  def test_als
    puts CeilingsAndFloors.meta.to_als
    assert CeilingsAndFloors.compile
  end

#  def test_run_show
 #   sol = Genealogy.run_show
  #  assert sol.satisfiable?
  #end
end
