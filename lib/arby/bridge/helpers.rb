module Arby
  module Bridge

    # ------------------------------------------------------------------
    # Various helper methods for dealing with Rjb::Proxy objects.
    # ------------------------------------------------------------------
    module Helpers
      # @param a4arr [Rjb::Proxy ~> Array]
      # @return [Array]
      def java_to_ruby_array(a4arr)
        size = a4arr.size
        (0...size).map{|i| a4arr.get(i)}
      end

      # @param a4arr [Rjb::Proxy ~> Array]
      # @return [Array]
      def jmap(a4arr, &block)
        java_to_ruby_array(a4arr).map(&block)
      end

      def jmap_iter(a4iterable, &block)
        a4iterator = a4iterable.iterator
        ans = []
        while a4iterator.hasNext
          t = a4iterator.next
          ans << yield(t)
        end
        ans
      end
    end
  end
end
