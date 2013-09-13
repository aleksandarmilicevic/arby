require 'my_test_helper'
require 'alloy/helpers/test/dsl_helpers'
require 'alloy/initializer.rb'

include Alloy::Dsl

alloy_model :A_M_FST do
  abstract sig Object
end

class FileSystemTest < Test::Unit::TestCase
  include Alloy::Helpers::Test::DslHelpers
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions

  include A_M_FST

  def setup_class
    Alloy.reset
    Alloy.meta.restrict_to(A_M_FST)
    Alloy.initializer.resolve_fields
    Alloy.initializer.init_inv_fields
  end

  def test
    # ans = A_M_ABT.delUndoesAdd
    # puts "#{ans}"
    # puts "-----------"
    # ans = A_M_ABT.delUndoesAdd_alloy
    # puts "#{ans}"
    puts Alloy.meta.to_als
  end
end
