require 'unit/alloy/alloy_test_helper.rb'

include Alloy::Dsl

module X
  alloy_model "Y" do
    sig D
  end
end

class TestAlloyUserModel < Test::Unit::TestCase
  include AlloyTestUtils

  def test1() create_module "MyModel1" end
  def test2() create_module :MyModel2 end
  
  def test_create_in_a_module
    assert_module_helper X::Y, "X::Y"
  end
  
  def test_invalid_name
    assert_raise(NameError) do
      create_module "My Model"
    end 
  end
      
  def test_already_defined
    mod = Alloy::Dsl::alloy_model("MyModel1")
    assert_equal MyModel1, mod
  end

end