#!/usr/bin/env ruby

GRAPH_DIR = "test/unit/arby/model/graphs"

puts "Test start"

Dir["#{GRAPH_DIR}/*.dat"].each do |f|
  puts `ruby -I"lib:test:.:../method_source/lib:../sdg_utils/lib" test/unit/arby/model/graph_tester.rb #{f} "find_maxIndependentSet"`
end

puts "Tests complete"
