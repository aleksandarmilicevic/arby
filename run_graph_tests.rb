#!/usr/bin/env ruby

GRAPH_DIR = "test/unit/arby/model/graphs"

algs = [
        #"maxCut",
        "maxIndependentSet", 
        #"maxCut", 
        #"minVertexCover"
       ]

algs.each do |alg|
  Dir["#{GRAPH_DIR}/*.dat"].each do |f|
    puts "Test start: #{alg} #{f}"
    puts `ruby -I"lib:test:.:../method_source/lib:../sdg_utils/lib" test/unit/arby/model/graph_tester.rb #{f} #{alg}`
    puts "Tests complete"
    puts ""
  end
end
