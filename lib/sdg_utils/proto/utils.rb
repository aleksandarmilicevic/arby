require 'sdg_utils/proxy'

module SDGUtils
  module Proto

    module Utils
      extend self

      def extend(&block)
        obj = SDGUtils::Proxy.new(self)
        singl_cls = (class << obj; self end)
        singl_cls.class_eval(&block)
      end
    end

  end
end
