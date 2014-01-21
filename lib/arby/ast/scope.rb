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
      def initialize(global=4, sig_scopes=[])
        @global = global || 4
        @sig_scopes = sig_scopes
      end

      def add_sig_scope(ss) @sig_scopes << ss end

      def extend_for_bounds(bnds)
        return unless bnds
        univ = bnds.extract_universe
        @global = [@global, univ.sig_atoms.group_by{|a|
                     a.class.meta.oldest_ancestor || a.class
                   }.map{|sig_cls, atoms|
                     atoms.size
                   }.max
                  ].max
      end

      def to_s(sig_namer=nil)
        global_scope = @global ? "#{@global} " : ''
        sig_scopes = @sig_scopes.map{|ss| ss.to_s(sig_namer)}.join(', ')
        sig_scopes = "but #{sig_scopes}" unless sig_scopes.empty?
        "for #{global_scope}#{sig_scopes}"
      end

      def to_als(sig_namer=Arby.conf.alloy_printer.sig_namer)
        global_scope = @global ? "#{@global} " : ''
        sig_scopes = @sig_scopes.map{|ss| ss.to_s(sig_namer)}.join(', ')
        sig_scopes = "but #{sig_scopes}" unless sig_scopes.empty?
        "for #{global_scope}#{sig_scopes}"
      end

    end

  end
end
