module Alloy
  module Dsl

    module AbstractHelper

      def abstract(blder, &block)
        blder.apply_modifier("abstract", nil, &block)
      end

    end

  end
end
