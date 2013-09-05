module SDGUtils

  module MDelegator
    # #TODO def respond_to?

    def method_missing(name, *args, &block)
      return super unless @target
      begin 
        # let the super method_missing run first (if defined)
        super
      rescue ::NameError
        handler = ::Proc.new do |*a, &b|
          obj = @target
          obj = @target.call() if ::Proc === @target && @target.arity == 0
          obj.send(name, *a, &b)
        end
        (class << self; self end).send :define_method, name, handler
        handler.call(*args, &block)
      end
    end
  end

  module MNested
    include MDelegator

    def self.included(base)
      base.class_eval <<-RUBY, __FILE__, __LINE__+1
        class << self
          private
          def new(*a, &b) super end
        end
        private
        def initialize(parent) @target = parent end
      RUBY
    end
  end

  class Delegator
    include MDelegator

    def initialize(obj)
      @target = obj
    end
  end

end
