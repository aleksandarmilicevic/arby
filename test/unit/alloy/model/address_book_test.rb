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

    fun do_add[n: Name, a: Addr][Book] {
      ans = Book.new
      ans.addr = addr + n*a
      ans
    }

    fun do_del[n: Name][Book] {
      ans = Book.new
      ans.addr = addr - n*a
      ans
    }

  end

  assertion delUndoesAdd {
    all [:b1, :b2, :b3] => Book, n: Name, a: Addr do
      if b1.addr[n].empty? && b1.add(b2, n, a) && b2.del(b3, n)
        b1.addr == b3.addr
      end
    end
  }

  assertion addIdempotent {
    all [b1, b2, b3] => Book, n: Name, a: Addr do
      if b1.add(b2, n, a) && b2.add(b3, n, a)
        b2.addr == b3.addr
      end
    end
  }

  assertion delUdoesAddF {
    all b1: Book, n: Name, a: Addr do
      b2 = b1.add(n, a)
      b3 = b2.del(n, a)
      b1 == b3
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
    ans = A_M_ABT.delUndoesAdd
    puts "#{ans}"
  end
end
