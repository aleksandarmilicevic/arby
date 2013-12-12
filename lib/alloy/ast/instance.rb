module Alloy
  module Ast
    class Instance

      # @param atoms [Array(Sig)]
      # @param fld_map [Hash(String, Array(Tuple)]    - field names to list of tuples
      # @param skolem_map [Hash(String, Array(Tuple)] - skolem names to list of tuples
      #    where Tuple is Array(Atom)
      def initialize(atoms, fld_map, skolem_map)
        @label2atom    = Hash[atoms.map{|a| [a.label, a]}]
        @fld2tuples    = fld_map.dup
        @skolem2tuples = skolem_map.dup

        ([@label2atom, @fld2tuples, @skolem2, self] +
          @fld2tuples.values + @skolem2tuples.values).each(&:freeze)
      end

      def atoms()      @label2atom.values end
      def fields()     @fld2tuples.keys end
      def skolems()    @skolem2tuples.keys end

      def atom(label)
        case label
        when Integer then label
        when String, Symbol
          label = label.to_s
          @label2atom[label] || (Integer(label) rescue nil)
        else
          fail "label must be either Integer, String or Symbol but is #{label.class}"
        end
      end
      def field(name)  @fld2tuples[name] end
      def skolem(name) @skolem2tuples[name] end

      def atom!(label)  atom(label) or fail("atom `#{label}' not found") end
      def field!(name)  field(name) or fail("field `#{name}' not found") end
      def skolem!(name) skolem(name) or fail("skolem `#{name}' not found") end

      alias_method :[], :atom
    end
  end
end

