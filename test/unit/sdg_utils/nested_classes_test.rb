require 'my_test_helper.rb'
require 'sdg_utils/proxy.rb'

module SDGUtils

  class NestedSuper
    def x() "NestedSuper.x" end
    def y() "NestedSuper.y" end

    def method_missing(sym, *a, &block)
      return super unless sym == :z
      "NestedSuper.z"
    end
  end

  class Parent
    def x() "Parent.x" end
    def y() "Parent.y" end
    def z() "Parent.z" end
    def u() "Parent.u" end

    def createNested() 
      Nested.send :new, self
    end

    class Nested < NestedSuper
      include SDGUtils::MNested
      def x()    "Nested.x" end
      def opx(x) x end
      def opy(y) y end
      def opz(z) z end
      def opu(u) u end
    end
  end

  class NestedClassesTest < Test::Unit::TestCase
    def setup
      @nested = Parent.new.createNested
    end

    def test_from_self
      assert_equal "Nested.x", @nested.x
    end

    def test_from_super
      assert_equal "NestedSuper.y", @nested.y
    end

    def test_from_super_missing
      assert_equal "NestedSuper.z", @nested.z
    end

    def test_from_parent
      assert_equal "Parent.u", @nested.u
    end

    def test_from_arg
      assert_equal "x", @nested.opx("x")
      assert_equal "y", @nested.opx("y")
      assert_equal "z", @nested.opx("z")
      assert_equal "u", @nested.opx("u")
    end

    def test_missing
      assert_raise(::NoMethodError) do 
        @nested.v
      end
    end
  end
end
