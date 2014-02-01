require 'my_test_helper'
require 'arby/helpers/test/dsl_helpers'
require 'arby/initializer.rb'
require 'arby/bridge/compiler'
require 'arby/bridge/solution'

require 'arby_models/alloy_sample/toys/birthday'

class BirthdayTest < Test::Unit::TestCase
  include Arby::Helpers::Test::DslHelpers
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions
  include Arby::Bridge

  Birthday = ArbyModels::AlloySample::Toys::Birthday
  include Birthday

  def setup_class
    Arby.reset
    Arby.meta.restrict_to(Birthday)
  end

  def test_als
    puts Birthday.meta.to_als
    assert Birthday.compile
  end

  def test_check_addWorks
    sol = Birthday.check_addWorks
    assert !sol.satisfiable?
  end

end
