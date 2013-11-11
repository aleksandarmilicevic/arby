require 'my_test_helper'
require 'alloy/helpers/test/dsl_helpers'
require 'alloy/initializer.rb'

include Alloy::Dsl

alloy :A_M_ABT do
  sig Name, Addr

  sig Book [
    addr: Name ** (lone Addr)
  ] do
    pred add[ans: Book, n: Name, a: Addr] {
      ans.addr == addr + n**a
    }

    pred del[ans: Book, n: Name] {
      ans.addr == addr - n**Addr
    }

    # fun do_add[n: Name, a: Addr][Book] {
    #   ans = Book.new
    #   ans.addr = addr + n**a
    #   ans
    # }

    # fun do_del[n: Name][Book] {
    #   ans = Book.new
    #   ans.addr = addr - n**a
    #   ans
    # }
  end

  assertion delUndoesAdd {
    all [:b1, :b2, :b3] => Book, n: Name, a: Addr do
      if b1.addr[n].empty? && b1.add(b2, n, a) && b2.del(b3, n)
        b1.addr == b3.addr
      end
    end
  }

  assertion addIdempotent {
    all [:b1, :b2, :b3] => Book, n: Name, a: Addr do
      if b1.add(b2, n, a) && b2.add(b3, n, a)
        b2.addr == b3.addr
      end
    end
  }

  # assertion delUdoesAddF {
  #   all b1: Book, n: Name, a: Addr do
  #     b2 = b1.add(n, a)
  #     b3 = b2.del(n, a)
  #     b1 == b3
  #   end
  # }
end

module A_M_ABT
  Expected_alloy = """
module A_M_ABT

sig Name  {}

sig Addr  {}

sig Book  {
  addr: Name -> Addr
}

pred add[self: Book, ans: Book, n: Name, a: Addr] {
  ans.addr = self.addr + n -> a
}

pred del[self: Book, ans: Book, n: Name] {
  ans.addr = self.addr - n -> Addr
}

assert delUndoesAdd {
  all b1: Book, b2: Book, b3: Book, n: Name, a: Addr {
    no b1.addr[n] && b1.add[b2, n, a] && b2.del[b3, n] => b1.addr = b3.addr
  }
}

assert addIdempotent {
  all b1: Book, b2: Book, b3: Book, n: Name, a: Addr {
    b1.add[b2, n, a] && b2.add[b3, n, a] => b2.addr = b3.addr
  }
}
"""
end

class AddressBookTest < Test::Unit::TestCase
  include Alloy::Helpers::Test::DslHelpers
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions

  include A_M_ABT

  def setup_class
    Alloy.reset
    Alloy.meta.restrict_to(A_M_ABT)
    Alloy.initializer.init_all_no_freeze
  end

  def test
    # ans = A_M_ABT.delUndoesAdd
    # puts "#{ans}"
    # puts "-----------"
    # ans = A_M_ABT.delUndoesAdd_alloy
    # puts "#{ans}"
    ans = Alloy.meta.to_als
    assert_equal A_M_ABT::Expected_alloy.strip, ans.strip
    puts ans
  end
end
