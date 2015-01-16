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
require 'sdg_utils/timing/timer'

module Test
  module Unit
    class TestCase
      def puts(*a) end
      def puts!(*a) Kernel.puts(*a) end
      # def teardown
      #   super
      #   puts! "=============--------------------~~~~~~~~~~~~~~~"
      #   puts! $perf_timer.print
      #   $perf_timer.summary.each {|k, v| puts! "#{k} => #{v}"}
      #   $perf_timer = SDGUtils::Timing::Timer.new
      #   # binding.pry
      # end
    end
  end
end

Arby.set_default :logger => Logger.new(NilIO.instance) # Logger.new(STDOUT)

# Arby.instrument_methods_for_timing(
#   "Arby::Bridge::Compiler.solve",
#   "Arby::Bridge::Compiler#solve",
#   "Arby::Bridge::Compiler.execute_command",
#   "Arby::Bridge::Compiler#execute_command",
#   "Arby::Bridge::Compiler#_parse",
#   "Arby::Ast::Model#to_als",
#   "Arby::Ast::Fun#__sym_exe",
#   "Arby::Ast::Expr::BinaryExpr.and",
#   "Arby::Ast::Expr::BinaryExpr.new",
#   # "Arby::Utils::AlloyPrinter#to_als",
#   # "Arby::Utils::AlloyPrinter#fun_to_als",
#   # "Arby::Utils::AlloyPrinter#command_to_als",
#   # "Arby::Utils::AlloyPrinter#field_to_als",
#   # "Arby::Utils::AlloyPrinter#type_to_als",
#   # "Arby::Utils::AlloyPrinter#arg_to_als",
#   # "Arby::Utils::AlloyPrinter#expr_to_als",
# )
