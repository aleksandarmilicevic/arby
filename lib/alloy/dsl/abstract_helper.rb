module Alloy
  module Dsl

    module AbstractHelper
      def abstract(sig_cls=nil, &block)
        if sig_cls
          sig_cls.meta.set_abstract
          sig_cls.class_evaluate(block) if block
        elsif block
          old_abstract = @abstract_alloy_block || false
          @abstract_alloy_block = true
          begin
            block.call
          ensure
            @abstract_alloy_block = old_abstract
          end
        else
          fail "neither class nor block provided"
        end
      end
    end

  end
end
