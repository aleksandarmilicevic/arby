require 'my_test_helper'
require 'arby_models/address_book'
require 'alloy/helpers/test/dsl_helpers'
require 'alloy/initializer.rb'
require 'alloy/bridge/compiler'


class AddressBookTest < Test::Unit::TestCase
  include Alloy::Helpers::Test::DslHelpers
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions

  include ArbyModels::AddressBook

  def setup_class
    Alloy.reset
    Alloy.meta.restrict_to(ArbyModels::AddressBook)
    Alloy.initializer.init_all_no_freeze

    @@als_model = Alloy.meta.to_als
    @@compiler  = Alloy::Bridge::Compiler.compile(@@als_model)
  end

  def test
    # ans = ArbyModels::AddressBook.delUndoesAdd
    # puts "#{ans}"
    # puts "-----------"
    # ans = ArbyModels::AddressBook.delUndoesAdd_alloy
    # puts "#{ans}"
    ans = Alloy.meta.to_als
    assert_equal_ignore_whitespace ArbyModels::AddressBook::Expected_alloy, ans
  end

  def test_check_addIdempotent
    sol = @@compiler.execute_command(:addIdempotent)
    assert !sol.satisfiable?
  end

  def test_check_delUndoesAdd
    sol = @@compiler.execute_command(:delUndoesAdd)
    assert !sol.satisfiable?
  end

  def test_find_model
    inst = Alloy.meta.solve_model
  end
end
