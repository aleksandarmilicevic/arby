module GraphModel
sig Node {val: lone Int}
sig Edge {src, dst: one Node}{src != dst}
sig Graph{nodes: set Node, edges: set Edge}

pred hampath[g: Graph, path: seq Node] {
 path[Int] = g.nodes
 #path = #g.nodes
 all i: Int | i >= 0 && i < minus[#path,1] => {
  some e: g.edges | 
   e.src = path[i] && e.dst = path[plus[i,1]] }
 }
 assert reach {
  all g: Graph, path: seq Node |
   hampath[g, path] => 
    g.nodes in path[0].*(~src.dst)
 }
run hampath for 5 but exactly 1 Graph, 3 Node
check reach for 5 but exactly 1 Graph, 3 Node

