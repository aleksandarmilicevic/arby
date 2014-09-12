require 'my_test_helper'
require 'arby_models/niki'

class NikiTest < Test::Unit::TestCase
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions

  include ArbyModels::NikiExample

  def setup_class
    Arby.reset
    Arby.meta.restrict_to(ArbyModels::NikiExample)
  end

  def test1
    a = Person.new(:name => "xyz")
    assert_set_equal ["xyz"], a.name 

    # everything is a set, that's why the following wouldn't work
    # assert_equal "xyz", a.name 

    assert_equal 124, a.inc(123)
    assert_set_equal [], a.friends.name    
  end

  def test2
    s = Student.new(:name => "qwer", :age => 23)
    assert_set_equal [23], s.age
    assert_equal 125, s.inc(123)    
  end

  def test3
    p1 = Person.new(:name => "p1")
    p2 = Person.new(:name => "p2")
    p3 = Person.new(:name => "p3")
    p1.friends = [p2, p3]

    assert_set_equal ["p2", "p3"], p1.friends.name
    
    s = Student.new(:friends => [p1, p2, p3])
    assert_set_equal ["p2", "p3", "p1"], s.friends.name
  end

  def test4
    p1 = Person.new(:name => "p1")    
    assert_raise(e: Exception) do
      p1.age = "23" # this should fail to typecheck and should immediatelly raise exception
    end
  end

end
