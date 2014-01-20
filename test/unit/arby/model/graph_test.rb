require 'my_test_helper'
require 'arby_models/graph'
require 'arby/helpers/test/dsl_helpers'
require 'arby/initializer.rb'
require 'arby/bridge/compiler'
require 'arby/bridge/solution'

class GraphTest < Test::Unit::TestCase
  include Arby::Helpers::Test::DslHelpers
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions
  include Arby::Bridge

  include ArbyModels::GraphModel

  def setup_class
    Arby.reset
    Arby.meta.restrict_to(ArbyModels::GraphModel)
  end

  def test_als
    puts Arby.meta.to_als
  end

  def test_ham
    n = 5
    vals = Array(0...n)
    nodes = vals.map{|i| Node.new :val => i}
    assert_equal vals, nodes.map(&:val)

    edges = (0...n-1).map{|i| Edge.new :src => nodes[i], :dst => nodes[i+1]}
    binding.pry
    g = Graph.new :nodes => nodes.shuffle, :edges => edges
    bnd = Arby::Ast::Instance.from_atoms(g).to_bounds
    sol = ArbyModels::GraphModel.solve :hamiltonian, n, bnd

    assert_equal vals, nodes.map(&:val)
    assert sol.satisfiable?
    inst = sol.arby_instance

binding.pry



  end

end
