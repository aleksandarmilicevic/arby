require 'my_test_helper'
require 'arby_models/abz14/graph'

class ABZ14GraphTest < Test::Unit::TestCase
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions
  include Arby::Bridge

  include ArbyModels::ABZ14::GraphModel

  def setup_class
    Arby.reset
    Arby.meta.restrict_to(ArbyModels::ABZ14::GraphModel)
  end

  def test1
    n1, n2 = Node.new, Node.new
    e = Edge.new src: n1, dst: n2
    g = Graph.new nodes: [n1, n2], edges: [e]
    hp = g.find_hampath # => [n1, n2]
    assert_equal [n1, n2], hp.unwrap
  end

end
