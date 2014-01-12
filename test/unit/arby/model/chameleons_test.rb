require 'my_test_helper'
require 'arby_models/chameleons'
require 'sdg_utils/timing/timer'

class ChameleonsTest < Test::Unit::TestCase
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions
  include Arby::Bridge

  include ArbyModels::ChameleonExample
  include ArbyModels::ChameleonExample::Chameleons

  def setup_class
    Arby.reset
    Arby.meta.restrict_to(ArbyModels::ChameleonExample)
    @@timer = SDGUtils::Timing::Timer.new
  end

  # def test_als
  #   puts ChameleonsViz.meta.to_als.inspect
  # end

  def test_chameleon
    puts Chameleons.meta.to_als
    sol = Chameleons.execute_command :some_meet
    assert sol.satisfiable?
    sol.arby_instance
  end

  def test_viz
    puts Viz.meta.to_als
    inst = Viz.find_instance
    assert inst
  end

  def test_chameleon_viz
    puts ChameleonsViz.meta.to_als
    sol = ChameleonsViz.execute_command :viz
    assert sol.satisfiable?
    sol.arby_instance
  end

  def test_staged
    puts "warming up: solving viz chameleons no bounds, scope: 5"
    viz_sol = @@timer.time_it {
      ChameleonsViz.solve :viz, 5, Chameleon => exactly(5-1)
    }
    puts "time: #{@@timer.last_time}"

    n = 9
    puts "scope = #{n}"

    puts "solving viz chameleons no bounds..."
    viz_sol = @@timer.time_it {
      ChameleonsViz.solve :viz, n, Chameleon => exactly(n-1)
    }
    t0 = @@timer.last_time
    puts "time: #{t0}"

    puts "solving chameleons..."
    ch_sol = @@timer.time_it {
      Chameleons.solve :some_meet, n, Chameleon => exactly(n-1)
    }
    t1 = @@timer.last_time
    puts "time: #{t1}"

    assert ch_sol.satisfiable?
    inst = ch_sol.arby_instance
    bounds = inst.to_bounds

    puts "solving viz for prev chameleons..."
    viz_sol = @@timer.time_it {
      ChameleonsViz.solve :viz, bounds, n
    }
    t2 = @@timer.last_time
    puts "time: #{t2}"
    puts "total: #{t1 + t2}"

    puts "solving viz chameleons no bounds..."
    viz_sol = @@timer.time_it {
      ChameleonsViz.solve :viz, n, Chameleon => exactly(n-1)
    }
    t3 = @@timer.last_time
    puts "time: #{t3}"
  end

  # def test_instance
  #   sol = ArbyModels::Grandpa.execute_command
  #   assert sol.satisfiable?
  #   inst = sol.arby_instance
  #   m = inst["$ownGrandpa_m"]
  #   assert m, "own grandpa skolem not found"
  #   assert m.in? parents(parents(m))
  # end

end
