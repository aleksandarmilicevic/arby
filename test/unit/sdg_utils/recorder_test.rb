require 'my_test_helper.rb'
require 'sdg_utils/recorder.rb'

module SDGUtils
  
  class RecorderTest < Test::Unit::TestCase
    
    def test0      
      r = SDGUtils::Recorder.new :var => ""      
      r.create_table :name do |x|
        x.column :name, "string", :default => "aca", :null => true
      end      
      expected= <<-EOS
create_table :name do |x| 
  x.column :name, "string", {:default=>"aca", :null=>true}
end
EOS
      assert_equal expected, r.to_s
    end
    
    def test1      
      r = SDGUtils::Recorder.new :var => "", :block_var => "x"      
      r.create_table :name do |x|
        x.column :name, "string", :default => "aca", :null => true
      end      
      expected= <<-EOS
create_table :name do |x| 
  x.column :name, "string", {:default=>"aca", :null=>true}
end
EOS
      assert_equal expected, r.to_s
    end
    
    def test2      
      r = SDGUtils::Recorder.new :var => "qwer", :block_var => "x"
      blck = Proc.new do |x, y|
        x.column :name, "string", :default => "aca", :null => true
        y.references :something
      end            
      r.create_table :name, &blck
      expected= <<-EOS
qwer.create_table :name do |x0, x1| 
  x0.column :name, "string", {:default=>"aca", :null=>true}
  x1.references :something
end
EOS
      assert_equal expected, r.to_s
    end

    def test3      
      r = SDGUtils::Recorder.new :var => "qwer", :block_vars => ["x", "y"]
      blck = Proc.new do |x, y|
        x.column :name, "string", :default => "aca", :null => true
        y.references :something
      end            
      r.create_table :name, &blck
      expected= <<-EOS
qwer.create_table :name do |x, y| 
  x.column :name, "string", {:default=>"aca", :null=>true}
  y.references :something
end
EOS
      assert_equal expected, r.to_s
    end    
    
    def test4      
      r = SDGUtils::Recorder.new :var => "qwer", :block_vars => ["x", "y", "z"]
      blck = Proc.new do |x, y|
        x.column :name, "string", :default => "aca", :null => true
        y.references :something
      end            
      r.create_table :name, &blck
      expected= <<-EOS
qwer.create_table :name do |x0, x1| 
  x0.column :name, "string", {:default=>"aca", :null=>true}
  x1.references :something
end
EOS
      assert_equal expected, r.to_s
    end 
  end
  
end
