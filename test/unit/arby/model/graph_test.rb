require 'my_test_helper'
require 'arby_models/graph'

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

  def test_als
    puts! GraphModel.meta.to_als
    assert GraphModel.compile
  end

  def test_exe_spec
    n1, n2 = Node.new, Node.new
    e = Edge.new src: n1, dst: n2
    g = Graph.new nodes: [n1, n2], edges: [e]
    hp = g.find_hampath # => [n1, n2]
    assert_equal [n1, n2], hp.unwrap

    hp = g.hampath.project(1) # => [n1, n2]
    assert_equal [n1, n2], hp.unwrap
  end

  def test_run_hampath
    sol = GraphModel.run_hampath
    assert sol.satisfiable?
    assert graph = sol["$hampath_g"]
    assert path  = sol["$hampath_path"]
    puts graph.nodes
    puts graph.edges
    puts path.project(1)
  end

  def test_check_reach
    sol = GraphModel.check_hampath_reach
    assert !sol.satisfiable? # assertion holds
  end

  def test_check_uniq
    sol = GraphModel.check_hampath_uniq
    assert !sol.satisfiable? # assertion holds
  end

  def test_k_color_props
    sol = GraphModel.check_kColor_props
    assert !sol.satisfiable? # assertion holds
  end

  def test_clique_props
    sol = GraphModel.check_clique_props
    assert !sol.satisfiable? # assertion holds
  end

  def test_noClique_sat
    sol = GraphModel.solve noClique { |g, n|
      n == 1
    }, *GraphModel::Scope5
    assert sol.satisfiable?
    g = sol[Graph].first
    assert g.nodes.empty?
  end

  def test_noClique_unsat
    sol = GraphModel.solve noClique { |g, n|
      some g.nodes and
      n == 1
    }, *GraphModel::Scope5
    assert !sol.satisfiable?
  end

  def test_maxClique_props
    sol = GraphModel.check_maxClique_props
    assert !sol.satisfiable? # assertion holds
  end

  def test_maxClique_sat1
    sol = GraphModel.solve maxClique { |g, clq|
      g.nodes.size == 2 and
      some g.edges
    }, *GraphModel::Scope5
    assert sol.satisfiable?
    clq = sol["$maxClique_clq"]
    assert_equal 2, clq.size
  end

  def test_maxClique_sat2
    sol = GraphModel.solve maxClique { |g, clq|
      some clq and
      g.nodes.size == clq.size
    }, *GraphModel::Scope5
    assert sol.satisfiable?
    g = sol["$maxClique_g"]
    assert_equal g.edges.size, g.nodes.size * (g.nodes.size - 1) / 2
  end

  def test_maxClique_unsat
    sol = GraphModel.solve maxClique { |g, clq|
      g.nodes.size < clq.size
    }, *GraphModel::Scope5
    assert !sol.satisfiable?
  end

  def test_maxClique_inst1
    n0, n1 = Node.new, Node.new
    g = Graph.new :nodes => [n0, n1],
                  :edges => [Edge.new(:src => n0, :dst => n1)]
    clq = g.find_maxClique
    assert_equal 2, clq.size
    assert_equal [n0, n1], clq.unwrap
  end

  def test_maxClique_inst2
    n0, n1, n2 = Node.new, Node.new, Node.new
    g = Graph.new :nodes => [n0, n1, n2],
                  :edges => [Edge.new(:src => n0, :dst => n1),
                             Edge.new(:src => n2, :dst => n1)]
    clq = g.find_maxClique
    assert_equal 2, clq.size
  end

  def test_maxClique_inst3
    n0, n1, n2 = Node.new, Node.new, Node.new
    g = Graph.new :nodes => [n0, n1, n2],
                  :edges => [Edge.new(:src => n0, :dst => n1),
                             Edge.new(:src => n2, :dst => n1)]
    pi = Arby::Ast::Bounds.from_atoms(g)
    sol = GraphModel.solve maxClique { |graph, clq|
      graph == g && clq.size > 2
    }, pi
    assert !sol.satisfiable?
  end

  def test_maxMaxClique_sat1
    sol = GraphModel.solve maxMaxClique { |g, clq|
      g.nodes.size == 2 and
      no g.edges and
      some(n1, n2: g.nodes) {
        n1 != n2 and
        some n1.val and
        some n2.val and
        n1.val != n2.val
      }
    }, *GraphModel::Scope5
    assert sol.satisfiable?
    clq = sol["$maxMaxClique_clq"]
    g = sol["$maxMaxClique_g"]
    assert_equal 1, clq.size
    assert_equal g.nodes.val.unwrap.max, clq.val.unwrap
  end

  def test_maxMaxClique_sat2
    sol = GraphModel.solve maxMaxClique { |g, clq|
      g.nodes.size == 3 and
      clq.size == 2 and
      all(n: g.nodes) { some n.val }
    }
    assert sol.satisfiable?
    clq = sol["$maxMaxClique_clq"]
    g = sol["$maxMaxClique_g"]
    assert_equal 2, clq.size
  end

  def test_maxMaxClique_inst1
    n0, n1, n2 = Node.new(1), Node.new(2), Node.new(3)
    g = Graph.new :nodes => [n0, n1, n2],
                  :edges => [Edge.new(:src => n0, :dst => n1),
                             Edge.new(:src => n0, :dst => n2)]
    clq = g.find_maxMaxClique
    assert_equal 2, clq.size
    assert_set_equal [n0, n2], clq
    assert_set_equal [1, 3], clq.val
  end

  def test_maxMaxClique_inst2
    n0, n1, n2 = Node.new(1), Node.new(2), Node.new(3)
    g = Graph.new :nodes => [n0, n1, n2],
                  :edges => [Edge.new(:src => n0, :dst => n1),
                             Edge.new(:src => n2, :dst => n1),
                             Edge.new(:src => n0, :dst => n2)]
    clq = g.find_maxMaxClique
    assert_equal 3, clq.size
    assert_set_equal [n0, n1, n2], clq
    assert_set_equal [1, 2, 3], clq.val
  end

  def test_maxMaxClique_inst3
    n0, n1, n2 = Node.new(1), Node.new(2), Node.new(3)
    g = Graph.new :nodes => [n0, n1, n2],
                  :edges => []
    clq = g.find_maxMaxClique
    assert_equal 1, clq.size
    assert_set_equal [n2], clq
    assert_set_equal [3], clq.val
  end

  def test_maxMaxClique_noinst1
    n0, n1, n2 = Node.new(1), Node.new(2), Node.new(3)
    g = Graph.new :nodes => [n0, n1, n2],
                  :edges => []
    clq = g.find_maxMaxClique { |g, clq| clq.size > 1 }
    assert !clq
  end


  def _test_guided
    sol = GraphModel.run_hampath
    assert sol.satisfiable?
    sol2 = sol.next { # "$hampath_path" != sol["$hampath_path"] &&
      g = sol[Graph].first
      Graph::nodes == sol[Graph::nodes] and
      Graph::edges == sol[Graph::edges] and
      (g.edges.< sol[Edge::dst]).in? Edge::dst and
      (g.edges.< sol[Edge::src]).in? Edge::src
    }
  end

end
