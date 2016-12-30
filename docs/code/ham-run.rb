# find an instance satisfying the :hampath pred
sol = GraphModel.run_hampath
assert sol.satisfiable?
g, path = sol["$hampath_g"], sol["$hampath_path"]
puts g.nodes # => e.g., {<Node$0>, <Node$1>}
puts g.edges # => e.g., {<Node$1, Node$0>}
puts path    # => {<0, Node$1>, <1, Node$0>}
# check that the "reach" assertion holds
sol = GraphModel.check_reach
assert !sol.satisfiable? 
