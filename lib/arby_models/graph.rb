require 'arby/arby_dsl'
require 'arby/ast/bounds'

module ArbyModels
  extend Arby::Dsl

  alloy :GraphModel do
    sig Node [val: (lone Int)]
    sig Edge [src, dst: (one Node)] {src != dst}
    sig Graph[nodes:(set Node), edges:(set Edge)] {
      this.edges.(src + dst).in? this.nodes
    }

    fun valsum[nodes: (set Node)][Int] {
      # sum(n: nodes) | n.val
      "sum n: nodes | n.val"
    }

    pred hampath[g: Graph, path: (seq Node)] {
      # path[Int] == g.nodes and
      # path.size == g.nodes.size and
      # all(i: 0...path.size-1) |
      #   some(e: g.edges) {
      #     e.src == path[i] and
      #     e.dst == path[i+1]
      #   }
"""
  path[Int] = g.nodes
  #path = #g.nodes
  all i: {i: Int | i >= 0 && i < minus[#path, 1]} {
    some e: g.edges {
      e.src = path[i]
      e.dst = path[(plus[i, 1])]
    }
  }
"""
    }

    pred kColor[g: Graph, k: Int, ans: Node ** (one Int)] {
      # ans.(Int) == g.nodes and
      # ans[Node].in? 0...k and
      # all(e: g.edges) {
      #   ans[e.src] != ans[e.dst]
      # }
"""
ans.Int = g.nodes
  ans[Node] in ({i: Int | i >= 0 && i < k})
  all e: g.edges {
    ans[e.src] != ans[e.dst]
  }
"""
    }

    pred independentSet[g: Graph, indset: (set Node)] {
      # indset.in? g.nodes and
      # all(n1: indset) |
      # all(n2: indset - n1) {
      #   no(e: g.edges) {
      #     (e.src == n1 && e.dst == n2) or
      #     (e.src == n2 && e.dst == n1)
      #   }
      # }
"""
indset in g.nodes
  all n1: indset {
    all n2: indset - n1 {
      no e: g.edges {
        e.src = n1 && e.dst = n2 || e.src = n2 && e.dst = n1
      }
    }
  }
"""
    }
 
    pred maxIndependentSet[g: Graph, indset: (set Node)] {
      # independentSet(g, indset) and
      # no(indset2: (set Node)) {
      #   indset2 != indset and
      #   independentSet(g, indset2) and
      #   indset2.size > indset.size
      # }
"""
independentSet[g, indset]
  no indset2: set Node {
    indset2 != indset
    independentSet[g, indset2]
    #indset2 > #indset
  }
"""
    }

    pred maxCut[g: Graph, cut: (set Node)] {
      # cut.in? g.nodes and
      # no(cut2: (set Node)) {
      #   cut2.in? g.nodes and
      #   cut2 != cut and
      #   crossing(g, cut2).size > crossing(g, cut).size
      # }
"""
cut in g.nodes
  no cut2: set Node {
    cut2 in g.nodes
    cut2 != cut
    (#crossing[g, cut2] > #crossing[g, cut] or
     (#crossing[g, cut2] = #crossing[g, cut] and #cut2 > #cut))
  }
"""
    }

    fun crossing[g: Graph, cut: (set Node)][(set Edge)] {
      # compl = g.nodes - cut

      # g.edges.select { 
      #   |e| (e.src.in? cut and e.dst.in? compl) or 
      #       (e.dst.in? cut and e.src.in? compl) }

      "{e: g.edges | (e.src in cut && e.dst in g.nodes - cut) || (e.dst in cut && e.src in g.nodes - cut)}"
    }

    pred minVertexCover[g: Graph, cover: (set Node)] {
      # vertexCover(g, cover) and
      # no(cover2: (set Node)) {
      #   cover != cover2	and
      #   vertexCover(g, cover2) and
      #   cover2.size < cover.size
      # }
"""
vertexCover[g, cover]
  no cover2: set Node {
    cover != cover2
    vertexCover[g, cover2]
    #cover2 < #cover
  }
"""
    }
    
    pred vertexCover[g: Graph, cover: (set Node)] {
      # cover.in? g.nodes and
      # all(e: g.edges) {
      #   e.src.in? cover or e.dst.in? cover
      # }	
"""
cover in g.nodes
  all e: g.edges {
    e.src in cover || e.dst in cover
  }
"""
    }

    pred clique[g: Graph, clq: (set Node)] {
      # clq.in? g.nodes and
      # all(n1: clq) |
      # all(n2: clq - n1) {
      #   some(e: g.edges) {
      #     (e.src == n1 && e.dst == n2) or
      #     (e.src == n2 && e.dst == n1)
      #   }
      # }
"""
clq in g.nodes
  all n1: clq {
    all n2: clq - n1 {
      some e: g.edges {
        e.src = n1 && e.dst = n2 || e.src = n2 && e.dst = n1
      }
    }
  }
"""
    }

    pred maxClique[g: Graph, clq: (set Node)] {
      # clique(g, clq) and
      # no(clq2: (set Node)) {
      #   clq2 != clq and
      #   clique(g, clq2) and
      #   clq2.size > clq.size
      # }
"""
clique[g, clq]
  no clq2: set Node {
    clq2 != clq
    clique[g, clq2]
    #clq2 > #clq
  }
"""
    }

    pred maxCliqueFix[g: Graph, clq: (set Node)] {
      "fix clique[g, clq] until #clq > #_clq"
    }

    pred maxMaxClique[g: Graph, clq: (set Node)] {
      # maxClique(g, clq) and
      # no(clq2: (set Node)) {
      #   clq2 != clq and
      #   maxClique(g, clq2) and
      #   valsum(clq2) > valsum(clq)
      # }
"""
  maxClique[g, clq]
  no clq2: set Node {
    clq2 != clq
    maxClique[g, clq2]
    valsum[clq2] > valsum[clq]
  }
"""
    }

    pred maxMaxCliqueFix[g: Graph, clq: (set Node)] {
      """
      fix maxClique[g, clq]
      until {
        valsum[clq] > valsum[_clq]
      }
      """
    }

    pred maxCliqueFixFix[g: Graph, clq: (set Node)] {
      """
      fix maxCliqueFix[g, clq]
      until {
        valsum[clq] > valsum[_clq]
      }
      """
    }

    # pred noSymEdges[g: Graph] {
    #   no(e1, e2: g.edges) {
    #     e1 != e2 and
    #     ((e1.src == e2.dst && e1.dst == e2.src) or
    #      (e1.src == e2.src && e1.dst == e2.dst))
    #   }
    # }

    # assertion hampath_reach {
    #   all(g: Graph, path: (seq Node)) |
    #     if hampath(g, path)
    #       g.nodes.in? path[0].*((~src).dst)
    #     end
    # }

    # assertion hampath_uniq {
    #   all(g: Graph, path: (seq Node)) |
    #     if hampath(g, path)
    #       all(n: g.nodes) { path.(n).size == 1 }
    #     end
    # }

    # assertion kColor_props {
    #   all(g: Graph, k: Int, ans: Node ** (one Int)) {
    #     if k > 0 && kColor(g, k, ans)
    #       ans.size == g.nodes.size and
    #       no(e: g.edges) { ans[e.src] == ans[e.dst] } and
    #       ans[Node].size <= k
    #     end
    #   }
    # }

    # assertion clique_props {
    #   all(g: Graph, clq: (set Node)) {
    #     n = clq.size
    #     if clique(g, clq) && noSymEdges[g]
    #       g.edges.select{|e| e.(src + dst).in? clq}.size == n*(n-1)/2
    #     end
    #   }
    # }

    # assertion maxClique_props {
    #   all(g: Graph, clq: (set Node)) {
    #     n = g.nodes.size
    #     if maxClique(g, clq) && n == clq.size && noSymEdges(g)
    #       g.edges.size == n*(n-1)/2
    #     end
    #   }
    # }

    # assertion maxClique_props {
    #   all(g: Graph, clq: (set Node)) {
    #     if g.nodes.size == 2 and some g.edges and maxClique(g, clq)
    #       g.nodes == clq
    #     end
    #   }
    # }


    self::Scope5 = [5, Int=>5, Graph=>exactly(1), Node=>5, Edge=>10]

    # run :hampath,         *Scope5
    # check :hampath_reach, *Scope5
    # check :hampath_uniq,  *Scope5

    # run :kColor,          *Scope5
    # check :kColor_props,  *Scope5

    # run :clique,          *Scope5
    # check :clique_props,  *Scope5

    # run :noClique,        *Scope5

    # check :maxClique_props, *Scope5

    # fix :clique, :max => lambda { |g, clq| clq.size }
  end

  # module GraphModel
  #   def no_clique(scope=Scope5)
  #     Arby.in_symbolic_mode do
  #       $pera = 2
  #       sol = solve noClique_1, *scope
  #       while sol.sat? do
  #         inst = sol.arby_instance
  #         g = inst[inst.skolems.first]
  #         s = g.edges.domain(inst[src])
  #         d = g.edges.domain(inst[dst])
  #         puts "candidate"
  #         puts "  nodes: " + g.nodes.to_s.gsub("\n", " ")
  #         puts "  edges: #{(~s).(d)}"
  #         # bnd = inst.to_bounds
  #         bnd = Arby::Ast::Bounds.fix_atoms(g)
  #         ch = solve noClique_2[g], bnd, *scope
  #         break if ch.pass?
  #         clq = ch[ch.skolems.first]
  #         binding.pry
  #         puts "finding next"
  #         sol = sol.next(:clq => clq) { |g|
  #           not (clq.size > 1 && clique(g, clq))
  #         }
  #       end
  #       if sol.sat?
  #         puts "solution found"
  #         puts sol
  #       else
  #         puts "no solution found"
  #       end
  #     end
  #   end
  # end

  class GraphModel::Graph
    def find_hampath
      bnds = Arby::Ast::Bounds.from_atoms(self)
      sol = GraphModel.solve :hampath, bnds
      if sol.satisfiable?
      then sol["$hampath_path"].project(1)
      else nil end
    end

    def find_hampath(&blk)         p=find_for(:hampath, :path, &blk) and p.project(1) end
    def find_maxClique(&blk)       find_for(:maxClique, :clq, &blk) end
    def find_maxIndependentSet(&blk)  find_for(:maxIndependentSet, :indset, &blk) end
    def find_maxCliqueFix(&blk)    find_for(:maxCliqueFix, :clq, &blk) end
    def find_minVertexCover(&blk)  find_for(:minVertexCover, :cover, &blk) end
    def find_maxCut(&blk)          find_for(:maxCut, :cut, &blk) end
    def find_maxMaxClique(&blk)    find_for(:maxMaxClique, :clq, &blk) end
    def find_maxMaxCliqueFix(&blk) find_for(:maxMaxCliqueFix, :clq, &blk) end

    def find_for(pred_name, out_var_name)
      bnds = Arby::Ast::Bounds.from_atoms(self)
#      bnds.bound_int (-8..7).to_a
      pred = if block_given?
               GraphModel.send(pred_name, &Proc.new)
             else
               pred_name
             end
      sol = GraphModel.solve pred, bnds, 4, Int => 0
      $arby_sol = sol
      if sol.satisfiable?
      then sol["$#{pred_name}_#{out_var_name}"]
      else nil end
    end
  end
  
end
