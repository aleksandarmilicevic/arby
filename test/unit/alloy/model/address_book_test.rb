require 'my_test_helper'
require 'arby_models/address_book'
require 'alloy/helpers/test/dsl_helpers'
require 'alloy/initializer.rb'


class AddressBookTest < Test::Unit::TestCase
  include Alloy::Helpers::Test::DslHelpers
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions

  include ArbyModels::AddressBook

  def setup_class
    Alloy.reset
    Alloy.meta.restrict_to(ArbyModels::AddressBook)
    Alloy.initializer.resolve_fields
    Alloy.initializer.init_inv_fields
  end

  def test
    # ans = ArbyModels::AddressBook.delUndoesAdd
    # puts "#{ans}"
    # puts "-----------"
    # ans = ArbyModels::AddressBook.delUndoesAdd_alloy
    # puts "#{ans}"
    ans = Alloy.meta.to_als
    assert_equal ArbyModels::AddressBook::Expected_alloy.strip, ans.strip
    puts ans
  end
end
