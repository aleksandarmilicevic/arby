# require 'my_test_helper'
# require 'arby/bridge/reporter'
# require 'arby_models/synth_joe'

# class GraphTest < Test::Unit::TestCase
#   include SDGUtils::Testing::SmartSetup
#   include SDGUtils::Testing::Assertions
#   include Arby::Bridge

#   SynthJoe = ArbyModels::SynthJoe
#   include SynthJoe

#   def setup_class
#     Arby.reset
#     Arby.meta.restrict_to(ArbyModels::SynthJoe)
#   end

#   def test_als
#     puts! SynthJoe.meta.to_als
#     assert SynthJoe.compile
#   end

#   def test_max3
#     # Arby.conf.do_with(reporter: Rep.new) do
#       Arby.conf.a4options.do_with(convertHolInst2A4Sol: true, holSome4AllMaxIter: 40) do
#         sol = SynthJoe.run_max3
#         assert sol.sat?
#         r = sol["$max3_root"]
#         puts! r.unwrap.prnt
#       end
#     end
#   # end
# end


# class Rep < Arby::Bridge::Reporter
#   include Arby::Bridge
#   def holLoopStart(tr, formula, bounds)
#     puts "start"
#   end
#   def holCandidateFound(tr, candidate)
#     puts "candidate found"
#   end
#   def holVerifyingCandidate(tr, candidate, checkFormula, bounds) end
#   def holCandidateVerified(tr, candidate) end
#   def holCandidateNotVerified(tr, candidate, cex) end
#   def holFindingNextCandidate(tr, inc) end
# end
