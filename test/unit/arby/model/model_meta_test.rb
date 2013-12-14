require 'my_test_helper'
require 'alloy/helpers/test/dsl_helpers'
require 'alloy/initializer.rb'

include Alloy::Dsl

alloy_model :A_M_MMT do
  sig A, {
    a: Int,
    b: String
  } do
    fun g {}
  end

  sig B < A

  pred p1 {
    true
  }

  fun f1 {
  }

  pred p2 {
  }

  def f2
  end
end

class ModelMetaTest < Test::Unit::TestCase
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions

  include A_M_MMT

  def setup_class
    Alloy.reset
    Alloy.meta.restrict_to(A_M_MMT)
    Alloy.initializer.init_all_no_freeze
  end

  def test
    assert A_M_MMT
    assert model=A_M_MMT.meta

    assert_seq_equal [A, B],     model.sigs
    assert_seq_equal [:p1, :p2], model.preds.map(&:name)
    assert_seq_equal [:f1, :f2], model.funs.map(&:name)

    assert_seq_equal ["a", "b"], model.sigs[0].meta.fields.map(&:name)
    assert_seq_equal [],         model.sigs[1].meta.fields
    assert_seq_equal ["a", "b"], model.sigs[1].meta.fields(false).map(&:name)

    assert_seq_equal [:g],       model.sigs[0].meta.funs.map(&:name)
    assert_seq_equal [],         model.sigs[1].meta.funs
    assert_seq_equal [:g],       model.sigs[1].meta.funs(false).map(&:name)
  end
end
