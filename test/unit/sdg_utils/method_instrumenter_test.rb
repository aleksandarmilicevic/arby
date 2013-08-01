require 'my_test_helper.rb'
require 'sdg_utils/proxy.rb'

module SDGUtils

  class MethodInstrumenterTest < Test::Unit::TestCase
    include SDGUtils::MethodInstrumenter

    def instr(n, instr_method, cb)
      x = (0...n).to_a
      c = class << x; self end
      send instr_method, x, /.*/, cb
      #send instr_method, x, /^[a-z_A-Z0-9]*$/, cb
      #send instr_method, x, /^size$/, cb
      {:method => instr_method, :obj => x, :cls => c, :cb => cb}
    end

    def test_around
      cls = Class.new do
        def calls() @calls ||= 0 end
        def call(name, args, block, &yield_cb)
          @calls = calls + 1
          yield_cb.call
        end
      end
      do_bench :around, cls
    end

    def test_before
      cls = Class.new do
        def calls() @calls ||= 0 end
        def call(name, args, block)
          @calls = calls + 1
        end
      end
      do_bench :before, cls
    end

    def test_after
      cls = Class.new do
        def calls() @calls ||= 0 end
        def call(name, args, block, value)
          @calls = calls + 1
        end
      end
      do_bench :after, cls
    end

    def do_bench(instr_method, cb_cls)
      n = 1000

      arr = %w(lambda send direct_call).map do |impl|
        instr n, "#{instr_method}_#{impl}".to_sym, cb_cls.new
      end

      bench = Proc.new do |m, &action|
        Benchmark.bm(30) do |reporter|
          arr.each do |hash|
            reporter.report("#{hash[:method]}: ") {m.times{action.call(hash[:obj])}}
          end
        end
      end

      expected = 0

      m = 100
      bench.call(m) {|x|
        ans = x.reduce(0){|a,e| a+e}
        assert_equal n*(n-1)/2, ans
        ans
      }

      expected += m*2
      arr.each do |hash|
        assert_equal expected, hash[:cb].calls
      end

      m = 10000
      bench.call(m) { |x|
        ans = x.size
        assert_equal n, ans
        ans
      }

      expected += m
      arr.each do |hash|
        assert_equal expected, hash[:cb].calls
      end

      bench.call(m) {|x| x << 1}

      expected += m
      arr.each do |hash|
        assert_equal expected, hash[:cb].calls
      end
      arr.each do |hash|
        assert_equal n+m, hash[:obj].size
      end
    end

  end
end
