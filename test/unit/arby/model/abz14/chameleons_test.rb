require 'my_test_helper'
require 'arby_models/abz14/chameleons'
require 'sdg_utils/timing/timer'

class ABZ14ChameleonsTest < Test::Unit::TestCase
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions
  include Arby::Bridge

  include ArbyModels::ABZ14
  include ArbyModels::ABZ14::Chameleons

  def setup_class
    Arby.reset
    Arby.meta.restrict_to(ArbyModels::ABZ14)
    @@timer = SDGUtils::Timing::Timer.new
  end

  # def test_als
  #   puts ChameleonsViz.meta.to_als.inspect
  # end

  def test_chameleon
    puts Chameleons.meta.to_als
    sol = Chameleons.solve :some_meet, 5, Chameleon => exactly(4)
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
    sol = ChameleonsViz.solve :viz, 5, Chameleon => exactly(4)
    assert sol.satisfiable?
    sol.arby_instance
  end

  def test_staged
    n = 5
    puts "scope = #{n}"
    puts "solving chameleons..."
    ch_sol = @@timer.time_it {
      Chameleons.solve :some_meet, n, Chameleon => exactly(n-1)
    }
    t1 = @@timer.last_time
    puts "time: #{t1}"
    assert ch_sol.satisfiable?

    inst = ch_sol.arby_instance
    bounds = inst.to_bounds

    times                        = inst[Time]
    chams                        = inst[Chameleon]
    projections                  = times.map{Viz::Projection.new}
    nodes                        = chams.map{Viz::Node.new}
    bounds[Viz::Projection]      = projections
    bounds[Viz::Projection.over] = projections * inst[Time]
    bounds[Viz::Node]            = nodes
    bounds.hi[Viz::Node.atom]    = (nodes * inst[Chameleon]) ** projections

    puts "solving viz for prev chameleons..."
    viz_sol = @@timer.time_it {
      ChameleonsViz.solve :viz, bounds, n
    }
    t2 = @@timer.last_time
    puts "time: #{t2}"
    puts "total: #{t1 + t2}"

    projections.each do |p|
      nodes.product(nodes).each do |n1, n2|
        c1 = n1.atom.(p)
        c2 = n2.atom.(p)
        same_kind = c1.color.(p.over) == c2.color.(p.over)
        same_color = n1.color.(p) == n2.color.(p)
        assert_equal same_kind, same_color
      end
    end
  end
end
