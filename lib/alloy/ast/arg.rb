require 'alloy/ast/types'
require 'alloy/ast/utils'

module Alloy
  module Ast

    # ----------------------------------------------------------------------
    # Holds meta information about args
    #
    # @attr name [String]
    # @attr type [AType]
    # @immutable
    # ----------------------------------------------------------------------
    class Arg
      include Checks

      attr_reader :name, :type

      class << self
        def getter_sym(fld)
          case fld
          when Alloy::Ast::Arg
            fld.name.to_sym
          when String
            fld.to_sym
          when Symbol
            fld
          else
            msg = "`fld' must be in [Field, String, Symbol], but is #{fld.class}"
            raise ArgumentError, msg
          end
        end

        def setter_sym(fld)
          "#{getter_sym(fld)}=".to_sym
        end
      end

      # Hash keys:
      #   :name [String]    - name
      #   :type [AType]     - type
      def initialize(hash)
        @name    = hash[:name]
        @type    = Alloy::Ast::AType.get(hash[:type])
        check_iden @name, "arg name"
      end

      def scalar?()            @type.scalar? end
      def primitive?()         scalar? && @type.range.primitive? end

      def getter_sym() Arg.getter_sym(self) end
      def setter_sym() Arg.setter_sym(self) end

      def to_s()
        "#{name}: #{type}"
      end

      def to_alloy
        "#{name.to_s}: #{type.to_alloy}"
      end

      def to_iden
        name.gsub /[^a-zA-Z0-9_]/, "_"
      end
    end

  end
end
