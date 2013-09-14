require 'sdg_utils/caching/searchable_attr'

module Alloy
  module Ast

    class Model
      include SDGUtils::Caching::SearchableAttr

      attr_reader :scope_module, :ruby_module, :name, :relative_name

      def initialize(scope_module, ruby_module)
        @scope_module = scope_module
        @ruby_module = ruby_module
        @name = scope_module.name
        @relative_name = @name.split("::").last

        init_searchable_attrs
      end

      attr_searchable :sig, :fun, :pred, :assertion, :fact, :command

      def all_funs() funs + preds + assertions + facts end
      def checks() commands.select{|c| c.check?} end
      def runs()   commands.select{|c| c.run?} end
    end

  end
end
