module SDGUtils

  class Delegator
    def initialize(obj)
      @target = obj
    end

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

  class Proxy < BasicObject
    def initialize(obj)
      @target = obj
    end

    def method_missing(name, *args, &block)
      return unless @target
      _get_handler(name).call(*args, &block)
    end

    protected

    def _get_handler(name)
      handler = ::Proc.new do |*a, &b|
        obj = @target
        obj = @target.call() if ::Proc === @target && @target.arity == 0
        obj.send(name, *a, &b)
      end
      (class << self; self end).send :define_method, name, handler
      handler
    end
  end

  class AroundProxy < Proxy
    def initialize(*args, &block) 
      @around_block = block
      super(*args)
    end

    def method_missing(name, *args, &block)
      @around_block.call(name, args, block, ::Proc.new do
        _get_handler(name).call(*args, &block)
      end)
    end
  end
end
