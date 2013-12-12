module Alloy
  module Ast

    # @attr label2atom [Hash(String, Sig)]                  - atom labels to atoms
    # @attr fld2tuples [Hash(String, Array(Array(Sig)))]    - atom labels to atoms
    class Instance

      # @param atoms [Array(AtomDecl)]
      # @param fld_map [Hash(String, Array(Tuple)]    - field names to list of tuples
      # @param skolem_map [Hash(String, Array(Tuple)] - skolem names to list of tuples
      #    where Tuple is Array(AtomDecl), and Atom is Alloy::Bridge::AtomDecl
      def initialize(atoms, fld_map, skolem_map)
        @label2atom    = Hash[atoms.map{|a|                [a.name, _create_atom(a)]}]
        @fld2tuples    = Hash[fld_map.map{|name, value|    [name, _to_set_proxy(value)]}]
        @skolem2tuples = Hash[skolem_map.map{|name, value| [name, _to_set_proxy(value)]}]

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

      private

      SIG_PREFIX = "this/"

      def _create_atom(atom_decl)
        sig_name = atom_decl.a4type.toString
        sig_name = sig_name[SIG_PREFIX.size..-1] if sig_name.start_with?(SIG_PREFIX)
        sig_cls = Alloy.meta.find_sig(sig_name)
        fail "sig #{sig_name} not found" unless sig_cls
        atom = sig_cls.new()
        atom.label = atom_decl.name
        atom
      end

      # @param tuples [Array(Array(Atom))]
      def _to_set_proxy(tuples)
        #TODO: finish - return SetProxy instead
        tuples.map{|t| t.map{|a| atom!(a.name)}}
      end
    end

  end
end

