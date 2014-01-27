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
    sol = ArbyModels::PrisonersHats.solve :allAmbig, 4, bnds
    if sol.satisfiable?
      inst = sol.arby_instance
      puts "colors: "
      puts inst[Prisoner.hatColor]

      # sol = sol.next do
      #   Prisoner::hatColor != inst[Prisoner.hatColor]
      # end

    end
  end


end
