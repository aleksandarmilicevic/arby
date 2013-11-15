
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
        (0...len).to_a.map do |idx|
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
    end
  end
end
