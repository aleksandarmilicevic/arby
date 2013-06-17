require 'my_test_helper.rb'
require 'alloy/relations/relation_ext'

include Alloy::Relations
    
module AlloyRelationTestHelper

  def assert_tuple(arr, t)
    assert_instance_of Tuple, t
    assert_equal arr.length, t.arity
    assert_equal arr, t.arr  
  end
  
  def rel_contains_tuple(rel, arr)
    x = rel.tuples.reject do |t|
      t.arr != arr
    end
    not x.empty?
  end
  
  def assert_empty_rel(arity, rel)
    assert_equal arity, rel.arity
    assert_equal 0, rel.length  
  end
  
  def assert_rel(arr, rel)
    assert_equal arr.length, rel.tuples.length
    arr.each do |t|
      assert rel_contains_tuple(rel, t)
    end
  end
  
end