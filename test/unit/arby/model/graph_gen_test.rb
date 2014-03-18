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
  
  def gen_random_graph(n)
    edge_threshold = 0.10
    g = []
    
    (0...n).each do |i|
      g[i] = []
      (0...n).each do |j|        
        if j <= i 
          g[i][j] = 0
        elsif rand > edge_threshold
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

  def test_random_maxClique_inst1
    @@find_max_clique_preds.each { |p| do_test_random_maxClique_inst1 p }    
  end

  def print_graph(g)
    puts! g.nodes
    g.edges.each do |e|
      puts! e.src.to_s + " --> " + e.dst.to_s
    end
  end

  def do_test_random_maxClique_inst1(pred_name)
    finder = Rjb::import('hola.MaxCliqueFinder')
    # Arby::Bridge::Imports.catch_alloy_errors {
    #   finder.findMaximumClique(a)
    # }

    (15...16).each do |n|
      a = gen_random_graph(n)   
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

# def gen_random_graph2(n)
#   edge_threshold = 0.25

#   nodes = (0...n).to_a.map { |i| Node.new }

#   edges = []
#   (0...n).each do |i|
#     (i+1...n).each do |j|
#       if rand > edge_threshold
#         edges << Edge.new(:src => nodes[i], :dst => nodes[j])
#       end
#     end
#   end

#   g = Graph.new :nodes => nodes, :edges => edges
#   while true do
#     r = connected(g)
#     if r[0] then break end
#     g = Graph.new :nodes => nodes, :edges => (edges << r[1])
#   end

#   g
# end


# # true iff n1 is reachable from n2 in g
# def reachable2(n1, n2, g, seen)
#   if n1 == n2 then return true end
#   if seen.include? n1 then return false end

#   seen << n1
#   g.edges.each do |e| 
#     if ((e.src == n1 && reachable(e.dst.tuples[0], n2, g, seen)) ||
#         (e.dst == n1 && reachable(e.src.tuples[0], n2, g, seen))) then
#       return true
#     end
#   end 
#   return false
# end

# # [true] if every pair of node in g is reachable from one another
# # [false, e] otherwise, where e is the new edge to add
# def connected2(g)
#   n = g.nodes.size 
#   (0...n).each do |i|
#     (i+1...n).each do |j|
#       n1 = g.nodes.tuples[i]
#       n2 = g.nodes.tuples[j]
#       seen = Set.new
#       if !reachable(n1, n2, g, seen) then           
#         return [false, Edge.new(:src => n1, :dst => n2)]
#       end
#     end
#   end
#   return [true]
# end
