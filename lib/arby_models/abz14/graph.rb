require 'arby/arby_dsl'
require 'arby/ast/bounds'

module ArbyModels
module ABZ14
  extend Arby::Dsl

  alloy_model :GraphModel do
    sig Node  [val: (lone Int)]
    sig Edge  [src, dst: Node, cost: (lone Int)]
    sig Graph [nodes: (set Node), edges: (set Edge)]

    pred hampath[g: Graph, ans: (seq Node)] {
     ans[Int] == g.nodes and
     all(i: 0...ans.size-1) |
      some(e: g.edges) {
       e.src == ans[i] && e.dst == ans[i+1]
      }
    }
  end

  class GraphModel::Graph
    def find_hampath
      bnds = Arby::Ast::Bounds.from_atoms(self)
      sol = GraphModel.solve :hampath, bnds
      if sol.satisfiable?
      then sol["$hampath_ans"].project(1)
      else nil end
    end
  end

end
end
