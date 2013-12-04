module Alloy
  module Ast
    class Instance

      # @param atoms [Array(Sig)]
      def initialize(atoms)
        @label2atom = Hash[atoms.map{|a| [a.label, a]}]
      end

      def size()      @label2atom.size end
      def atom(label) @label2atom[label] end

      alias_method :[], :atom
    end
  end
end

