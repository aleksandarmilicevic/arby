require 'arby/ast/types'
require 'arby/ast/utils'

module Arby
  module Ast

    class SigScope
      attr_reader :sig, :scope, :exact
      def initialize(sig, scope, exact=false)
        @sig, @scope, @exact = sig, scope, exact
      end

      def exact?() !!@exact end

      def to_s(sig_namer=nil)
        sig_namer ||= proc{|s| s.relative_name}
        "#{@exact ? 'exactly ' : ''}#{@scope} #{sig_namer[@sig]}"
      end
    end

    class Scope
      attr_reader :global, :sig_scopes
      def initialize(global, sig_scopes=[])
        @global = global || 4
        @sig_scopes = sig_scopes
      end

      def add_sig_scope(ss) @sig_scopes << ss end

      def to_s(sig_namer=nil)
        global_scope = @global ? "#{@global} " : ''
        sig_scopes = @sig_scopes.map{|ss| ss.to_s(sig_namer)}.join(' ')
        "for #{global_scope}#{sig_scopes}"
      end
    end

  end
end
