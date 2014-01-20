require 'arby/arby_dsl'

module ArbyModels
  extend Arby::Dsl

  alloy_model :GraphModel do

    sig Node [
      val: Int
    ]

    sig Edge [
      src: Node,
      dst: Node,
      cost: Int
    ]

    sig Graph [
      nodes: (set Node),
      edges: (set Edge)
    ]

    pred hamiltonian[g: Graph, ans: (seq Node)] {
      ans[Int] == g.nodes and
      all(i: 0...ans.size-1) {
        some(e: g.edges) { e.src == ans[i] && e.dst == ans[i+1] }
      }
    }

    pred hamiltonian2[g: Graph, ans: (seq Edge)] {
      ans[Int].in? g.edges and
      ans[Int].src + ans[Int].dst == g.nodes and
      ans[Int].size == g.nodes.size - 1 and
      all(i: 0...ans.size-1) { ans[i].dst == ans[i+1].src }
    }

  end
end
