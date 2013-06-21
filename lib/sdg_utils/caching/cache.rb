module SDGUtils
  module Caching

    class Cache
      attr_reader :hits, :misses, :name

      def initialize(name="", hash={})
        @name = name
        @cache = {}
        @hits = 0
        @misses = 0
        @on_miss = lambda{|*args|}
        @on_hit = lambda{|*args|}
        @fake = hash[:fake]
      end

      def fetch(key, &block)
        if !@fake && ans = @cache[key]
          @hits += 1
          @on_hit.call(self, key, ans)
          ans
        else
          @misses += 1
          @on_miss.call(self, key)
          ans = block.call()
          @cache[key] = ans unless @fake
          ans
        end
      end

      def on_miss(&block) @on_miss = wrap_block(block); self end
      def on_hit(&block)  @on_hit = wrap_block(block); self end

      def fake?() @fake end

      private

      def wrap_block(block)
        case
        when block.arity == 0
          lambda{|*args| block.call}
        when block.arity == -1
          block
        else
          lambda { |*args|
            bargs = (0...block.arity).map {|i| args[i]}
            block.call(*bargs)
          }
        end
      end
    end

  end
end
