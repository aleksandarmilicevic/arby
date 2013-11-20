require 'alloy/bridge/imports'

module Alloy
  module Bridge
    module Translator
      extend self

      SIG_PREFIX = "this/"

      # Takes an Rjb Proxy object pointing to a list of alloy atoms,
      # and converts them to instances of corresponding aRby sig
      # classes.
      #
      # @param a4atoms [Rjb::Proxy -> SafeList<ExprVar>]
      # @return [Array(Sig)]
      def translate_atoms(a4atoms)
        len = a4atoms.size
        (0...len).map do |idx|
          translate_atom(a4atoms.get(idx))
        end
      end

      # Takes an Rjb Proxy object pointing to an alloy atom, and
      # converts it to an instance of the corresponding aRby sig
      # class.
      #
      # @param a4atom [Rjb::Proxy -> ExprVar]
      # @return [Sig]
      def translate_atom(a4atom)
        sig_name = a4atom.type.toExpr.toString
        sig_name = sig_name[SIG_PREFIX.size..-1] if sig_name.start_with?(SIG_PREFIX)
        sig_cls = Alloy.meta.find_sig(sig_name)
        fail "sig #{sig_name} not found" unless sig_cls
        atom = sig_cls.new()
        atom.label = a4atom.toString
        atom
      end

      def recreate_object_graph(map, atoms)
       atoms.each do |atom|

       #arby_field = atom.meta.field(name) #TODO figure out what name is
       #atom.write_field(arby_field,"value") #TODO figure out what the value is
       #keys in map are the relation type
         map.each do |key, value|
          # each key represent a relation type between two atoms
          # value a list of tuples, each list has 2 atoms
          # each atom has a name (String) and a type
          # for each atom in the map I should find the matched atom in
          # atoms and based on the relation I should add a arby field and
          #write that field and its value

          #issue what is name in field?
          # it is based on this       def [](sym) field(sym.to_s) end
          # every value I tried gave me nil

          #issue 2 what is value in write_field
          #issue 3 is fld , is the same as the arby_field?
          #question can translate_atoms be incorporated into this method
         end
        end
      end


    end
  end
end
