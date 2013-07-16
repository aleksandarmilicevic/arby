require 'sdg_utils/print_utils/tree_printer.rb'

module SDGUtils
  module Timing

    class Timer

      class Node
        attr_reader :task, :children, :parent
        attr_accessor :time
        def initialize(task, parent=nil)
          @task = task
          @parent = parent
          @children = []
          parent.children << self if parent
        end
      end

      def initialize
        @stack = []
        @root = Node.new("ROOT")

        @tree_printer = SDGUtils::PrintUtils::TreePrinter.new({
          :indent_size => 2,
          :print_root  => false,
          :printer     => lambda {|node| "#{node.task}: #{node.time * 1000}ms"},
          :descender   => lambda {|node| node.children + unaccounted(node)},
        })
      end

      def unaccounted(node)
        return [] if node.time.nil? || node.children.empty?
        ans = Node.new("*** Unaccounted time ***")
        ans.time = node.time - node.children.reduce(0){|acc, ch| acc + ch.time}
        [ans]
      end

      def time_it(task, &block)
        parent = @stack.last || @root
        node = Node.new(task, parent)
        begin
          @stack.push node
          ans = nil
          node.time = Benchmark.realtime{ans = yield}
          ans
        ensure
          @stack.pop
        end
      end

      def print
        @tree_printer.print_tree(@root)
      end
    end

  end
end
