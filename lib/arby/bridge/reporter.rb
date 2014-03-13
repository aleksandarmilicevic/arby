module Arby
  module Bridge

    class Reporter
      def debug(msg) end
      def parse(msg) end
      def typecheck(msg) end
      def warning(msg) end
      def scope(msg) end
      def bound(msg) end
      def generatingSolution(fgoal, bounds) end
      def translate(solver, bitwidth, maxseq, skolemDepth, symmetry) end
      def solve(primaryVars, totalVars, clauses) end
      def resultCNF(filename) end
      def resultSAT(command, solvingTime, solution) end
      def minimizing(command, before) end
      def minimized(command, before, after) end
      def resultUNSAT(command, solvingTime, solution) end
      def write(expr) end

      def holLoopStart(tr, formula, bounds) end
      def holCandidateFound(tr, candidate)  end
      def holVerifyingCandidate(tr, candidate, checkFormula, bounds) end
      def holCandidateVerified(tr, candidate) end
      def holCandidateNotVerified(tr, candidate, cex) end
      def holFindingNextCandidate(tr, inc) end

      def holSplitStart(tr, formula) end
      def holSplitChoice(tr, formula, bounds) end
      def holSplitChoiceSAT(tr, inst) end
      def holSplitChoiceUNSAT(tr) end
    end

  end
end
