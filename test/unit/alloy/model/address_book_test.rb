require 'unit/alloy/alloy_test_helper.rb'
require 'alloy/initializer.rb'
require 'sdg_utils/lambda/proc'

include Alloy::Dsl


alloy_model :A_M_ABT do
  sig Name, Addr

  sig Book, {
    addr: Name * (lone Addr)
  } do
    pred add[ans: Book, n: Name, a: Addr] {
      ans.addr == addr + n*a
    }

    pred del[ans: Book, n: Name] {
      ans.addr == addr - n*Addr
    }
  end

  assertion delUndoesAdd {
    all [:b1, :b2, :b3] => Book, :n => Name, :a => Addr do

    end
  }
end

class String
  include SDGUtils::Lambda::Str2Proc
end

class AddressBookTest < Test::Unit::TestCase
  include AlloyTestUtils
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions

  include A_M_ABT

  def setup_class
    Alloy.reset
    Alloy.meta.restrict_to(A_M_ABT)
    Alloy.initializer.resolve_fields
    Alloy.initializer.init_inv_fields
  end

  def test
    # puts A_M_ABT.delUndoesAdd
  end
end
