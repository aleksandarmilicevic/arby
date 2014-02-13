$LOAD_PATH.unshift File.expand_path('../../../sdg_utils/lib', __FILE__)
$LOAD_PATH.unshift File.expand_path('../../../method_source/lib', __FILE__)
$LOAD_PATH.unshift File.expand_path('../..', __FILE__)
$LOAD_PATH.unshift File.expand_path('../../lib', __FILE__)

require 'logger'
require 'nilio'
require 'set'
require 'test/unit'
require 'pry'

require 'arby/arby'
require 'sdg_utils/testing/assertions'
require 'sdg_utils/testing/smart_setup'

module Test
  module Unit
    class TestCase
      def puts(*a) end
      def puts!(*a) Kernel.puts(*a) end
    end
  end
end

Arby.set_default :logger => Logger.new(NilIO.instance) # Logger.new(STDOUT)
