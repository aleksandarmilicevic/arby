require 'my_test_helper'
require 'arby_models/graph'
require 'set'
require 'benchmark'
require 'rjb'
require 'arby/bridge/imports'

class GraphTest < Test::Unit::TestCase
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions
  include Arby::Bridge

  GraphModel = ArbyModels::GraphModel
  include GraphModel

  GRAPH_DIR = "test/unit/arby/model/graphs"

  def setup_class
    Arby.reset
    Arby.meta.restrict_to(ArbyModels::GraphModel)
  end

  # def test_als
  #   puts! GraphModel.meta.to_als
  #   assert GraphModel.compile
  # end

  @@max_clique_preds = [:maxClique] #, :maxCliqueFix]
  @@find_max_clique_preds = [:find_maxClique] #, :find_maxCliqueFix]

  # returns the set of neighbours of node n in graph g
  def neighbours(n, g)
    ns = Set.new
    g.edges.each do |e| 
      if e.src == n then
        ns = ns << e.dst.tuples[0]
      elsif e.dst == n then
        ns = ns << e.src.tuples[0]
      end
    end
    ns
  end

  # Uses Bron-Kerbosch algorithm to find a maximal clique
  # http://en.wikipedia.org/wiki/Bron-Kerbosch_algorithm    
  def find_maximal_clique(r, p, x, g, cs)
    if p.empty? and x.empty? then
      cs << r
      return
    end
    
    p.clone.each do |n|
      ns = neighbours(n, g)
      find_maximal_clique(r + [n], p & ns, x & ns, g, cs)   
      p = p - [n]
      x = x + n      
    end
  end

  def find_maximum_clique(g)    
    r = Set.new
    p = Set.new g.nodes
    x = Set.new 
    cliques = Set.new
    find_maximal_clique(r, p, x, g, cliques)

    max = nil
    cliques.each do |c|
      if !max || c.size > max.size
        max = c
      end
    end
    return max
  end

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

  # true iff n1 is reachable from n2 in g
  def reachable(n1, n2, g, seen)
    if n1 == n2 then return true end
    if seen.include? n1 then return false end
    
    seen << n1
    n = g.size 
    (0...n).each do |i|
      (i+1...n).each do |j|
        if g[i][j] == 1
          if i == n1 && reachable(j, n2, g, seen) then return true end
        end
      end
    end
    return false
  end
  
  # [true] if every pair of node in g is reachable from one another
  # [false, e] otherwise, where e is the new edge to add
  def connected(g)
    n = g.size 
    (0...n).each do |i|
      (i+1...n).each do |j|
        seen = Set.new
        if !reachable(i, j, g, seen)
          return [false, i, j]
        end
      end
    end
    
    return [true]
  end
  
  def gen_random_graph(n, threshold)
    g = []
    
    (0...n).each do |i|
      g[i] = []
      (0...n).each do |j|        
        if j <= i 
          g[i][j] = 0
        elsif rand > threshold
          g[i][j] = 1
        else
          g[i][j] = 0
        end
      end
    end
    while true do
      r = connected(g)
      if r[0] then break end
      g[r[1]][r[2]] = 1
    end
    g
  end

  # def test_maxClique
  #   @@find_max_clique_preds.each { 
  #     |p| run_graph_tests(p, 
  #                        [4, 5], 
  #                        [0.1, 0.3, 0.5, 0.7, 0.9]) 
  #   }
  # end

  def test_graph_gen
    gen_graphs([35, 40, 45, 50], [0.1, 0.3, 0.5, 0.7, 0.9], 5)
#    gen_graphs([2, 3, 4], [0.3, 0.5, 0.7], 3)
  end

  def print_graph(g)
    puts! g.nodes
    g.edges.each do |e|
      puts! e.src.to_s + " --> " + e.dst.to_s
    end
  end

  # g: graph, represented as double array, with 1 representing an edge
  # fname: name of the file to write into
  def dump_graph(g, fname, threshold, run_id) 
    n = g.size    
    File.open(fname, 'w') do |f|
      f.puts(n)
      f.puts threshold
      f.puts run_id
      g.each do |row|
        f.puts(row)
      end
      f.close
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

  def gen_graphs(sizes, thresholds, num)
    (1..num).each do |n|
      sizes.each do |s|
        thresholds.each do |t|
          g = gen_random_graph(s, t)
          dump_graph(g,"#{GRAPH_DIR}/s#{s}_t#{(t*100).to_i}_n#{n}.dat", t, n)
        end
      end    
    end    
  end

  # def test_graphs_from_files
  #   @@find_max_clique_preds.each { |p| run_graph_tests_from_files(p) }
  # end

  def run_graph_tests_from_files(alg_name, graph_dir=GRAPH_DIR) 
    Dir["#{GRAPH_DIR}/*.dat"].each do |f|      
      g = convert_to_arby_graph(read_graph(f)[0])
      Benchmark.bm do |x|        
        x.report("#{f}: ") { alloy_clq = g.send(alg_name) }
      end              
    end   
  end

  # alg_name: the name of the function that runs the algorithm
  # sizes: sizes of graph to be tested
  # thresholds: thresholds to be used for graph generation
  def run_graph_tests(alg_name, sizes, thresholds)
    
    sizes.each do |s|
      thresholds.each do |t|
        a = gen_random_graph(s, t)   
        g = convert_to_arby_graph(a)
        Benchmark.bm do |x|        
          x.report("s=#{s},t=#{t}: ") { alloy_clq = g.send(alg_name) }
        end        
      end
    end

  end

  # def test_random_maxClique_inst1
  #   @@find_max_clique_preds.each { |p| do_test_random_maxClique_inst1 p }    
  # end

  def do_test_random_maxClique_inst1(pred_name)
    finder = Rjb::import('hola.MaxCliqueFinder')
    # Arby::Bridge::Imports.catch_alloy_errors {
    #   finder.findMaximumClique(a)
    # }

    (1...10).each do |n|
      a = gen_random_graph(n, 0.5)   
      g = convert_to_arby_graph(a)
      puts! "Graph size: #{n}"
      impl_clq = nil
      alloy_clq = nil
      Benchmark.bm do |x|        
        x.report("HOLA: ") { alloy_clq = g.send(pred_name) }
      end
      ret = finder.findMaximumClique(a)     
      impl_clq = ret.toArray.map {|e| "Node__#{e.intValue}"}

      print_graph(g) 
      puts! "Alloy: #{alloy_clq}"
      puts! "Bron-Kerbosch: #{impl_clq.inspect}"
      puts! "\n"
      if alloy_clq.size != impl_clq.size then
        puts! "Something is wrong! n = #{n}"
        return
      end      
    end    
  end

end
