#!/usr/bin/env ruby

GRAPH_DIR = "test/unit/arby/model/graphs"

Dir["#{GRAPH_DIR}/*.dat"].each do |f|
  puts "Testing graph from file #{f}"
  puts `ruby -I"lib:test:.:../method_source/lib:../sdg_utils/lib" test/unit/arby/model/graph_tester.rb #{f}`
end

puts "Tests complete."
