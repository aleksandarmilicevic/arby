require 'my_test_helper'
require 'arby/helpers/test/dsl_helpers'
require 'arby/helpers/test/test_event_listener'
require 'arby/initializer.rb'

include Arby::Dsl

module AFAE
  alloy_model do
    sig SBase, {
      r: SBase,
    } do
      abstract

      def initialize(name)
        @name = name
      end

      def to_s
        @name.to_s
      end
    end

    sig SigA < SBase, {
      i: Integer,
      s: String,
      f: Float,
      b: Bool
    } do
      def initialize(name)
        super
      end
    end
  end
end

class AlloyFldAccessEventsTest < Test::Unit::TestCase
  include Arby::Helpers::Test::DslHelpers
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions

  def setup_class
    Arby.reset
    Arby.meta.restrict_to(AFAE)
    Arby.initializer.init_all_no_freeze
  end

  def setup_test
    if @listener; Arby.boss.unregister_listener(@listener) end
    @listener = Arby::Helpers::Test::TestEventListener.new
    Arby.boss.register_listener(:field_read, @listener)
    Arby.boss.register_listener(:field_written, @listener)
  end

  def test1
    a = AFAE::SigA.new('x')
    a.i = 4
    x = a.b
    a.b = false
    x = a.b
    AFAE::SigA.new('y').b
    assert_arry_equal ["x.b -> {}","x.b -> {<false>}","y.b -> {}"], @listener.format_reads
    assert_arry_equal ["x.i <- 4", "x.b <- false"], @listener.format_writes
  end

end
