require 'arby/arby_dsl'
require 'arby/ast/bounds'

module ArbyModels
  extend Arby::Dsl

  alloy :GraphModel do
    sig Node [val: (lone Int)]
    sig Edge [src, dst: (one Node)] {src != dst}
    sig Graph[nodes:(set Node), edges:(set Edge)]

    pred hampath[g: Graph, path: (seq Node)] {
      path[Int] == g.nodes and
      path.size == g.nodes.size and
      all(i: 0...path.size-1) |
        some(e: g.edges) {
          e.src == path[i] and
          e.dst == path[i+1]
        }
    }

    pred kColor[g: Graph, k: Int, ans: Node ** (one Int)] {
      ans.(Int) == g.nodes and
      ans[Node].in? 0...k and
      all(e: g.edges) {
        ans[e.src] != ans[e.dst]
      }
    }

    pred clique[g: Graph, clq: (set Node)] {
      clq.in? g.nodes and
      all(n1: clq) |
      all(n2: clq - n1) {
        some(e: g.edges) {
          (e.src == n1 && e.dst == n2) or
          (e.src == n2 && e.dst == n1)
        }
      }
    }

    pred max_clique[g: Graph, clq: (set Node)] {
      clique(g, clq) # and max!(clq.size)
    }

    # pred no_clique[g: Graph] {
    #   no(clq: (set Node)) | clique(g, clq)
    # }

    pred noSymEdges[g: Graph] {
      no(e1, e2: g.edges) {
        e1 != e2 and
        ((e1.src == e2.dst && e1.dst == e2.src) or
         (e1.src == e2.src && e1.dst == e2.dst))
      }
    }

    assertion hampath_reach {
      all(g: Graph, path: (seq Node)) |
        if hampath(g, path)
          g.nodes.in? path[0].*((~src).dst)
        end
    }

    assertion hampath_uniq {
      all(g: Graph, path: (seq Node)) |
        if hampath(g, path)
          all(n: g.nodes) { path.(n).size == 1 }
        end
    }

    assertion kColor_props {
      all(g: Graph, k: Int, ans: Node ** (one Int)) {
        if k > 0 && kColor(g, k, ans)
          ans.size == g.nodes.size and
          no(e: g.edges) { ans[e.src] == ans[e.dst] } and
          ans[Node].size <= k
        end
      }
    }

    assertion clique_props {
      all(g: Graph, clq: (set Node)) {
        n = clq.size
        if clique(g, clq) && noSymEdges[g]
          g.edges.select{|e| e.(src + dst).in? clq}.size == n*(n-1)/2
        end
      }
    }

    Scope5 = [5, Int=>6, Graph=>exactly(1), Node=>5, Edge=>10]

    run :hampath,         *Scope5
    check :hampath_reach, *Scope5
    check :hampath_uniq,  *Scope5

    run :kColor,          *Scope5
    check :kColor_props,  *Scope5

    run :clique,          *Scope5
    check :clique_props,  *Scope5

    # fix :clique, :max => lambda { |g, clq| clq.size }
  end

  module GraphModel
    def no_clique
      sol = run_clique
    end
  end

  class GraphModel::Graph
    def find_hampath
      bnds = Arby::Ast::Bounds.from_atoms(self)
      sol = GraphModel.solve :hampath, bnds
      if sol.satisfiable?
      then sol["$hampath_path"].project(1)
      else nil end
    end
  end

end
