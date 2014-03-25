require 'arby_models/graph'
require 'set'
require 'benchmark'
require 'rjb'
require 'arby/bridge/imports'
require 'pry'

def puts!(s) 
  puts s
end

class GraphTester 
  include Arby::Bridge

  GraphModel = ArbyModels::GraphModel
  include GraphModel

  RESULT_DIR = "test/unit/arby/model/results_graph"

  def setup_class
    Arby.reset
    Arby.meta.restrict_to(ArbyModels::GraphModel)
  end

  @@ref_impls = {
    :maxClique => 'run_rjb_max_clique_finder',
    :maxMaxClique => 'run_rjb_max_max_clique_finder',
    :maxIndependentSet => 'run_rjb_max_indset_finder',
    :maxCut => 'run_rjb_max_cut_finder',
    :minVertexCover => 'run_rjb_min_vertex_cover_finder',
  }

  @@arby_calls = {
    :maxClique => 'find_maxClique',
    :maxMaxClique => 'find_maxMaxClique',
    :maxIndependentSet => 'find_maxIndependentSet',
    :maxCut => 'find_maxCut',
    :minVertexCover => 'find_minVertexCover'
  }

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

    # # debug
    # alloy_str = ""
    # g.nodes.each do |n|
    #   alloy_str += "#{n}, "
    # end
    # alloy_str += "\n"
    # g.edges.each do |e|
    #   alloy_str += "#{e}, "      
    # end
    # alloy_str += "\n"
    # alloy_str += "src = "
    # g.edges.each do |e|
    #   alloy_str += "#{e} -> #{e.src} + "      
    # end
    # alloy_str += "\n"
    # alloy_str += "dst = "
    # g.edges.each do |e|
    #   alloy_str += "#{e} -> #{e.dst} + "      
    # end
    # alloy_str += "\n"
    # puts! alloy_str
  
    alloy_ret = nil
    arby_alg = @@arby_calls[alg_name]

    m = Benchmark.measure { alloy_ret = g.send(arby_alg) }
    fio = File.open("#{RESULT_DIR}/#{alg_name}", 'a')

    # some extra stats
    solving_time = $arby_sol.solving_time
    num_cands = $arby_sol._a4sol.getStats().numCandidates()
    sat_solving_time = $arby_sol._a4sol.getStats().solvingTime()

    # print the stats to file and console
    print_line("#{size},#{threshold},#{run_id},#{m.total},#{solving_time}," + 
               "#{sat_solving_time/1000.0},#{num_cands}", 
               fio)

    # run the Java reference implementation
    rjb_fun = @@ref_impls[alg_name]
    rjb_ret = self.send(rjb_fun, a, alloy_ret)    
  end
  
  def run_rjb_max_clique_finder(g, arby_sol)
    finder = Rjb::import('hola.MaxCliqueFinder')
    ret = nil
    Arby::Bridge::Imports.catch_alloy_errors {
      ret = finder.findMaximumClique(g)
    }
    ref_sol = ret.toArray.map {|e| "Node__#{e.intValue}"}

    if arby_sol.size != ref_sol.size then
      test_fail_msg("Failed maxClique test!", arby_sol, ref_sol)
      exit
    else
      puts "Test passed"
    end
  end

  def run_rjb_max_max_clique_finder(g, arby_sol)
  end

  def run_rjb_max_indset_finder(g, arby_sol)
    finder = Rjb::import('hola.MaxIndependentSetFinder')
    ret = nil
    Arby::Bridge::Imports.catch_alloy_errors {
      ret = finder.findMaxIndependentSet(g)
    }
    ref_sol = ret.toArray.map {|e| "Node__#{e.intValue}"}

    if arby_sol.size != ref_sol.size then
      test_fail_msg("Failed maxIndependentSet test!", arby_sol, ref_sol)
      exit
    else
      puts "Test passed"
    end
  end

  def run_rjb_max_cut_finder(g, arby_sol)
    finder = Rjb::import('hola.MaxCutFinder')
    ret = nil
    Arby::Bridge::Imports.catch_alloy_errors {
      ret = finder.findMaximumCut(g)
    }
    ref_sol = ret.toArray.map {|e| "Node__#{e.intValue}"}

    if arby_sol.size != ref_sol.size then 
      test_fail_msg("Failed maxCut test!", arby_sol, ref_sol)
      exit
    else
      puts "Test passed"
    end
  end

  def run_rjb_min_vertex_cover_finder(g, arby_sol)
    finder = Rjb::import('hola.MinVertexCoverFinder')
    ret = nil
    Arby::Bridge::Imports.catch_alloy_errors {
      ret = finder.findMinVertexCover(g)
    }
    ref_sol = ret.toArray.map {|e| "Node__#{e.intValue}"}

    if arby_sol.size != ref_sol.size then
      test_fail_msg("Failed minVertexCover test!", arby_sol, ref_sol)
      exit
    else
      puts "Test passed"
    end
  end

  def test_fail_msg(msg, arby_sol, ref_sol) 
    puts! "***************** TEST FAILUER *****************"
    puts! msg
    puts! "Arby: #{arby_sol}"
    puts! "Reference: #{ref_sol}"
  end

end

tester = GraphTester.new
tester.test_graph_from_file(ARGV[0], ARGV[1])
