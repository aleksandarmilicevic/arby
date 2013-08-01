require 'unit/alloy/alloy_test_helper.rb'
require_relative 'alloy_dsl_sig_test_tmpl.rb'

tmpl = get_test_template('AlloyDslSigTest', 'Alloy::Dsl::alloy_model', 'Alloy::Dsl::Model.sig', 'Alloy::Ast::Sig')
eval tmpl

# require_relative 'alloy_dsl_sig_test_tmpl.rb'
# module MDslSigTest
  # class DslSigTest < TestDslSigTmpl
    # def self.model_func; "Alloy::Dsl::alloy_model" end
    # def self.sig_func; "sig" end
#
    # self.init_once
  # end
# end


=begin
 include Alloy::Dsl

alloy_model do
  sig S
  sig :S_sym
end

alloy_model "X" do
  sig S
  sig :S_sym
end

module M
  alloy_model do
    sig S
    sig :S_sym
  end

  alloy_model "X" do
    sig S
    sig :S_sym
  end

  module N
    alloy_model do
      sig S
      sig :S_sym
    end

    alloy_model "X" do
      sig S
      sig :S_sym
    end
  end
end

class TestAlloyDslSig < Test::Unit::TestCase
  include AlloyTestUtils

  def test_sig_inner1
    alloy_module do
      sig :Inner
    end
    sig_test_helper('Inner')
  end

  def test_sig_inner2
    alloy_module "I" do
      sig :Inner
    end
    sig_test_helper('I::Inner')
  end

  def test_create_sig_global
    sig_test_helper('S')
    sig_test_helper('S_sym')
  end

  def test_create_sig_module
    sig_test_helper('X::S')
    sig_test_helper('X::S_sym')
  end

  def test_create_sig_nested_module
    sig_test_helper('M::S')
    sig_test_helper('M::S_sym')
  end

  def test_create_sig_nested_module2
    sig_test_helper('M::X::S')
    sig_test_helper('M::X::S_sym')
  end

  def test_create_sig_nested_module3
    sig_test_helper('M::N::X::S')
    sig_test_helper('M::N::X::S_sym')
  end

  def test_no_override1
    assert_raise(NameError) do
      Alloy::Dsl::alloy_module do
        sig S
      end
    end
    assert_raise(NameError) do
      Alloy::Dsl::alloy_module do
        sig :S_sym
      end
    end
  end

  def test_no_override2
    assert_raise(NameError) do
      Alloy::Dsl::alloy_module "X" do
        sig S
      end
    end
    assert_raise(NameError) do
      Alloy::Dsl::alloy_module "X" do
        sig :S_sym
      end
    end
  end

  def test_empty_name
    assert_raise(NameError) do
      sig nil
    end
    assert_raise(NameError) do
      sig ""
    end
  end

  def test_invalid_name
    assert_raise(NameError) do
      sig "  "
    end
    assert_raise(NameError) do
      sig :x
    end
  end

  def test_base_sig_ok
    assert_nothing_raised do
      Alloy::Dsl::alloy_model do
        sig :X1 < S
        sig :X2 < X::S
        sig :X3 < M::X::S
      end
    end
  end

  def test_base_sig_not_sig1
    assert_raise(Alloy::Ast::TypeError) do
      Alloy::Dsl::alloy_model do; sig :X4 < String end
    end
  end

  def test_base_sig_not_sig2
    assert_raise(Alloy::Ast::TypeError) do
      Alloy::Dsl::alloy_model do; sig :X5 < Alloy::Ast::Sig end
    end
  end

  def test_base_sig_not_class
    assert_raise(ArgumentError) do
      Alloy::Dsl::alloy_model do; sig :X6 < "KJdf" end
    end
    assert_raise(ArgumentError) do
      Alloy::Dsl::alloy_model do; sig :X7 < 1 end
    end
    assert_raise(ArgumentError) do
      Alloy::Dsl::alloy_model do; sig :X8 < :X8 end
    end
  end
end
=end