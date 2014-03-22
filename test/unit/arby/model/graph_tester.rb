require 'arby_models/graph'
require 'set'
require 'benchmark'
require 'rjb'
require 'arby/bridge/imports'

class GraphTester 
  include Arby::Bridge

  GraphModel = ArbyModels::GraphModel
  include GraphModel

  def setup_class
    Arby.reset
    Arby.meta.restrict_to(ArbyModels::GraphModel)
  end

  @@max_clique_preds = [:maxClique] #, :maxCliqueFix]
  @@find_max_clique_preds = [:find_maxClique] #, :find_maxCliqueFix]

  def convert_to_arby_graph(g)
    n = g.size
    nodes = (0...n).to_a.map { |i| Node.new }
    edges = []
    (0...n).each do |i|
      (i+1...n).each do |j|
        if g[i][j] == 1 then 
          edges << Edge.new(:src => nodes[i], :dst => nodes[j])
        end
      end
    end
    Graph.new :nodes => nodes, :edges => edges
  end

  def print_graph(g)
    puts! g.nodes
    g.edges.each do |e|
      puts! e.src.to_s + " --> " + e.dst.to_s
    end
  end

  def read_graph(fname)
    g = []
    size, threshold, run_id = 0, 0, 0
    File.open(fname, 'r') do |f|
      size = f.gets.to_i
      threshold = f.gets.to_i
      run_id = f.gets.to_i
      (0...size).each do |i|
        g[i] = []
        (0...size).each do |j|
          g[i][j] = f.gets.to_i
        end
      end
    end 
    return [g, size, threshold, run_id]
  end

  def test_graph_from_file(f)
    @@find_max_clique_preds.each { |p| do_graph_test_from_file(p, f) }
  end

  def do_graph_test_from_file(alg_name, f)
    g = convert_to_arby_graph(read_graph(f)[0])
    Benchmark.bm do |x|        
      x.report("#{f}: ") { alloy_clq = g.send(alg_name) }
    end
  end

end

tester = GraphTester.new
ARGV.each do |fname|
  tester.test_graph_from_file(fname)
end
