module SDGUtils
  module PrintUtils
    
    class TreePrinter

      def initialize(hash={})
        @indent_size = hash[:indent_size] || 2
        @printer = hash[:printer] || lambda{|node| node.to_s}
        @descender = hash[:descender] || lambda{|node| node.children}
        @print_root = hash.key?(:print_root) ? hash[:print_root] : true

        @tab1 = "|"
        @tab2 = "`"
        @indent_size.times{
          @tab1.concat " ";
          @tab2.concat "-"
        }
      end

      def print_tree(node, depth=0)
        node_out = ""
        unless depth== 0 && !@print_root
          node_str = @printer.call(node)
          lines = (Array === node_str ? node_str : node_str.split("\n"))
          ind = indent(depth)
          node_out = lines.reduce("") { |acc, line|
            acc.concat(ind).concat(line).concat("\n")
          }
        end
        @descender.call(node).reduce(node_out) { |acc, child|
          acc.concat(print_tree(child, depth+1))
        }
      end

      private 

      def indent(depth)
        (0...depth-1).reduce("") {|acc,i| acc.concat (i == depth-2 ? @tab2 : @tab1)}
      end


    end
    
  end
end
