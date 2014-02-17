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

  def test_no_clique
    GraphModel.no_clique
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
