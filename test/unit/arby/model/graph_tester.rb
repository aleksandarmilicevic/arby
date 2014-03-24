require 'arby_models/graph'
require 'set'
require 'benchmark'
require 'rjb'
require 'arby/bridge/imports'
require 'pry'

class GraphTester 
  include Arby::Bridge

  GraphModel = ArbyModels::GraphModel
  include GraphModel

  RESULT_DIR = "test/unit/arby/model/results_graph"

  def setup_class
    Arby.reset
    Arby.meta.restrict_to(ArbyModels::GraphModel)
  end

  @@ref_impls = {}

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
      threshold = f.gets.to_f
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

  def print_line(l, fio=nil)  
    if fio then fio.puts l end
    puts l
  end

  def test_graph_from_file(f, alg)    
    do_graph_test_from_file(alg.to_sym, f) 
  end

  def do_graph_test_from_file(alg_name, f)
    # run the Alloy version
    a, size, threshold, run_id = read_graph(f)
    g = convert_to_arby_graph(a)
    alloy_ret = nil
    m = Benchmark.measure { alloy_ret = g.send(alg_name) }
    fio = File.open("#{RESULT_DIR}/#{alg_name}", 'a')
    solving_time = $arby_sol.solving_time
    num_cands = $arby_sol._a4sol.getStats().numCandidates()
    sat_solving_time = $arby_sol._a4sol.getStats().solvingTime()
    print_line("#{size}\t#{threshold}\t#{run_id}\t#{m.total}\t#{solving_time}\t#{sat_solving_time/1000.0}\t#{num_cands}", fio)

    # run the Java reference implementation
    rjb_ret = run_rjb_max_indset_finder(a)
    
    if alloy_ret.size != rjb_ret.size then
      puts! "Something is wrong!"
      return
    end
  end
  
  def run_rjb_max_indset_finder(g)
    finder = Rjb::import('hola.MaxIndependentSetFinder')
    ret = nil
    Arby::Bridge::Imports.catch_alloy_errors {
      ret = finder.findMaxIndependentSet(g)
    }
    return ret.toArray.map {|e| "Node__#{e.intValue}"}
  end

end

tester = GraphTester.new
tester.test_graph_from_file(ARGV[0], ARGV[1])
