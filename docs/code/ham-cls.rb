module GraphModel
 class Node;  attr_accessor :val end
 class Edge;  attr_accessor :src, :dst end
 class Graph; attr_accessor :nodes, :edges end

 def self.hampath(g, path) <same as above> end
 def self.reach()          <same as above> end
 def self.run_hampath() exe_cmd :hampath end
 def self.check_reach() exe_cmd :reach end
end
