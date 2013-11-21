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
         map.each do |key, value|
          name = key
          values =[] # this may be buggy need to test
          for tuple in value
            rhs = extract_atom(atoms,tuple[0].name)
            lhs = extract_atom(atoms,tuple[1].name)
            field = rhs.meta.field(name)
            if field.scalar?
              rhs.write_field(field,lhs)
            else
              values.push(lhs)
              rhs.write_field(field,values)
            end
          end         
        end
      end

      def extract_atom(atoms, label)
          return atoms.select { |atom|  atom.label == label }.first
      end


    end
  end
end
