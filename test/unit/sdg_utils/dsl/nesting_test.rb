require 'my_test_helper.rb'
require 'sdg_utils/dsl/class_builder'
require 'sdg_utils/dsl/module_builder'
require 'sdg_utils/dsl/ext'

require_relative '../nested_classes_test'

module SDGUtils
  module DSL

    def self.mod(*args, &block)
      SDGUtils::DSL::ModuleBuilder.new().build(*args, &block)
    end

    mod :NestedTest do
      def self.cls(*args, &block)
        SDGUtils::DSL::ClassBuilder.new().build(*args, &block)
      end

      cls NestedSuper do
        def x() "NestedSuper.x" end
        def y() "NestedSuper.y" end

        def method_missing(sym, *a, &block)
          return super unless sym == :z
          "NestedSuper.z"
        end
      end

      cls Parent do
        def self.cls(*args, &block) NestedTest.cls(*args, &block) end

        def x() "Parent.x" end
        def y() "Parent.y" end
        def z() "Parent.z" end
        def u() "Parent.u" end

        cls Nested < NestedSuper do
          def x()    "Nested.x" end
          def opx(x) x end
          def opy(y) y end
          def opz(z) z end
          def opu(u) u end
        end
      end
    end

    class DSLNestedClassesTest < Test::Unit::TestCase
      include SDGUtils::NestedClassesTestMethods
      def setup
        @nested = NestedTest::Parent.new.new(NestedTest::Parent::Nested)
      end
    end

  end
end
