require 'my_test_helper'
require 'arby_models/prisoners_hats'
require 'arby/helpers/test/dsl_helpers'
require 'arby/initializer.rb'
require 'arby/bridge/compiler'
require 'arby/bridge/solution'

class PrisonersHatsTest < Test::Unit::TestCase
  include Arby::Helpers::Test::DslHelpers
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions
  include Arby::Bridge

  include ArbyModels::PrisonersHats

  def setup_class
    Arby.reset
    Arby.meta.restrict_to(ArbyModels::PrisonersHats)
  end

  def test_als
    puts ArbyModels::PrisonersHats.to_als
    assert ArbyModels::PrisonersHats.compile
  end

  def test_s1
    pr = 4.times.map{Prisoner.new}
    bnds = Arby::Ast::Bounds.new
    bnds[Prisoner] = pr
    bnds[Prisoner::first] = pr.first
    bnds[Prisoner::next] = (0...pr.size-1).map{|i| [pr[i],  pr[i+1]]}
    sol = ArbyModels::PrisonersHats.solve :allAmbig, 4, bnds
    while sol.satisfiable?
      inst = sol.arby_instance
      puts "colors: "
      puts inst[Prisoner.hatColor]
      sol = sol.next { Prisoner::hatColor != inst[Prisoner.hatColor] }
    end
    sol = sol.model.solve :allAmbigExcept, 4, bnds
    while sol.satisfiable?
      certain = sol['$allAmbigExcept_certain']
      colors = sol[Prisoner.hatColor]
      puts "if #{colors}"
      puts "#{certain} deduced his own hat color: #{certain.deduced1[certain]}"
      sol = sol.next { Prisoner::hatColor != inst[Prisoner.hatColor] }
    end
    binding.pry
  end


end
