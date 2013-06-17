require 'unit/alloy/alloy_test_helper.rb'
require 'alloy/initializer.rb'
require_relative 'alloy_event_listener'

include Alloy::Dsl

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
  include AlloyTestUtils
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions
   
  def setup_class    
    Alloy.reset
    Alloy.meta.restrict_to(AFAE)
    Alloy.initializer.resolve_fields    
  end
  
  def setup_test
    if @listener; Alloy.boss.unregister_listener(@listener) end
    @listener = AlloyTestEventListener.new
    Alloy.boss.register_listener(:field_read, @listener)
    Alloy.boss.register_listener(:field_written, @listener)
  end
  
  def test1
    a = AFAE::SigA.new('x')
    a.i = 4
    x = a.b
    a.b = false
    x = a.b
    AFAE::SigA.new('y').b
    assert_arry_equal ["x.b -> nil", "x.b -> false", "y.b -> nil"], @listener.format_reads
    assert_arry_equal ["x.i <- 4", "x.b <- false"], @listener.format_writes
  end
    
end