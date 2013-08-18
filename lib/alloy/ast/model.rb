module Alloy
  module Ast

    class Model
      attr_reader :ruby_module, :name, :relative_name

      def initialize(ruby_module, name)
        @ruby_module = ruby_module
        @name = name
        @relative_name = @name.split("::").last
        @sigs = []
        @preds = []
      end

      def sig_created(sig)
      end
    end

  end
end
