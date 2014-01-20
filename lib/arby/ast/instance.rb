require 'arby/ast/bounds'
require 'arby/ast/tuple_set'

module Arby
  module Ast

    # @typeparam Atom     - anything that responds to :label
    # @typeparam TupleSet - any array-like class
    #
    # @attr label2atom [Hash(String, Atom)]        - atom labels to atoms
    # @attr fld2tuples [Hash(String, TupleSet)]    - field names to tuples
    # @attr skolem2tuples [Hash(String, TupleSet)] - skolem names to tuples
    class Instance

      def self.from_atoms(*atoms)
        all_atoms = ASig.all_reachable_atoms(atoms)
        fld_map = {}
        all_atoms.each do |a|
          if ASig === a
            sig = a.class
            sig.meta.fields(false).each do |fld|
              ts = fld_map[fld] ||= TupleSet.wrap([], fld.full_type)
              ts.union!([a] ** a.read_field(fld))
            end
          end
        end
        Instance.new(all_atoms, fld_map, {}, false)
      end

      # @param atoms [Array(Atom)]
      # @param fld_map [Hash(String, TupleSet]    - field names to list of tuples
      # @param skolem_map [Hash(String, TupleSet] - skolem names to list of tuples
      def initialize(atoms=[], fld_map={}, skolem_map={}, dup=true, model=nil)
        @model         = model
        @atoms         = dup ? atoms.dup : atoms
        @label2atom    = Hash[atoms.map{|a| [a.label, a]}]
        @type2atoms    = atoms.group_by(&:class)
        @fld2tuples    = dup ? fld_map.dup : fld_map
        @skolem2tuples = dup ? skolem_map.dup : skolem_map

        ([@label2atom, @type2atoms, @fld2tuples, @skolem2, self] +
          @fld2tuples.values + @skolem2tuples.values).each(&:freeze)
      end

      def model()      @model end
      def atoms()      @atoms end
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
      def field(fld)   @fld2tuples[fld] end
      def skolem(name) @skolem2tuples[name] end

      def atom!(label)  atom(label)  or fail("atom `#{label}' not found") end
      def field!(fld)   field(fld)   or fail("field `#{fld}' not found") end
      def skolem!(name) skolem(name) or fail("skolem `#{name}' not found") end

      def [](key)
        case key
        when Class then @type2atoms[key] || []
        when Field then field(key)
        else
          atom(key) || skolem(key) || field(key)
        end
      end

      def to_bounds
        bounds = Bounds.new
        atoms.group_by(&:class).each do |cls, atoms|
          bounds.bound_exactly(cls, atoms) if cls < Arby::Ast::ASig
        end
        @fld2tuples.each{|fld, ts| bounds.bound_exactly(fld, ts)}
        bounds
      end

      def to_s
        atoms_str = atoms.map(&:label).join(', ')
        "atoms:\n  #{atoms_str}\n" +
          "fields:\n  #{@fld2tuples}\n" +
          "skolems:\n  #{@skolem2tuples}"
      end
    end

  end
end

