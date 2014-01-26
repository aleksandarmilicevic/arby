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

  # def test_s1
  #   sol = ArbyModels::PrisonersHats.solve :deducedRight, 4
  #   if sol.satisfiable?
  #     inst = sol.arby_instance
  #     p = inst[inst.skolems.first]
  #     bnd = inst.to_bounds
  #     bnd.add_lower(Prisoner.deduced, p ** p ** Color)
      
  #     binding.pry
  #   end
  # end

  def test_s1
    pr = 4.times.map{Prisoner.new}
    bnds = Arby::Ast::Bounds.new
    bnds[Prisoner] = pr
    sol = ArbyModels::PrisonersHats.solve :allAmbig, 4, bnds
    if sol.satisfiable?
      inst = sol.arby_instance
      puts "colors: "
      puts inst[Prisoner.hatColor]

      sol = sol.next do
        Prisoner.hatColor != inst[Prisoner.hatColor]
      end

      binding.pry
      sol = ArbyModels::PrisonersHats.solve :allAmbig, 4, bnds
      binding.pry
    end
  end


end
