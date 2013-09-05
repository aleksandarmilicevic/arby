module SDGUtils

  module MDelegator
    # #TODO def respond_to?

    def method_missing(name, *args, &block)
      return unless @target
      handler = ::Proc.new do |*a, &b|
        obj = @target
        obj = @target.call() if ::Proc === @target && @target.arity == 0
        obj.send(name, *a, &b)
      end
      (class << self; self end).send :define_method, name, handler
      handler.call(*args, &block)
    end
  end

  class Delegator
    include MDelegator

    def initialize(obj)
      @target = obj
    end
  end

end
