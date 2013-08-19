require 'sdg_utils/caching/searchable_attr'

module Alloy
  module Ast

    class Model
      include SDGUtils::Caching::SearchableAttr

      attr_reader :ruby_module, :name, :relative_name

      def initialize(ruby_module, name)
        @ruby_module = ruby_module
        @name = name
        @relative_name = @name.split("::").last

        init_searchable_attrs
      end

      attr_searchable :sig, :fun, :pred, :assertion, :fact
    end

  end
end
