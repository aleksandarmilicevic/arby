require 'sdg_utils/random'

module SDGUtils

  class Proxy
    instance_methods.each { |m| undef_method m unless m =~ /(^__|^send$|^object_id$)/ }

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
      @around_block.call(name, args, block, ::Proc.new{
        _get_handler(name).call(*args, &block)
      })
    end
  end

  class MethodInstrumenter
    def self.around_object_methods(obj, name_pattern=/.*/, &block)
      self.around_instance_methods(class << obj; self end, name_pattern, &block)
    end

    def self.around_instance_methods(cls, name_pattern=/.*/, &block)
      mthds = cls.instance_methods.reject{|m|
        /(^__|^send$|^object_id$)/ === m
      }.grep(name_pattern)
      mthds.each{|m|
        alias_sym = "__#{Time.now.utc.strftime("%s_%L")}__#{m}".to_sym
        cls.send :alias_method, alias_sym, m
        cls.send :define_method, m, lambda{|*a, &b|
          block.call(m, a, b) {
            self.send alias_sym, *a, &b
          }
        }
      }
    end

#     def self.around_instance_methods2(cls, name_pattern=/.*/, &block)
#       mthds = cls.instance_methods.reject{|m|
#         /(^__|^send$|^object_id$)/ === m
#       }.grep(name_pattern)
#       mthds.each{|m|
#         rand = SDGUtils::Random.salted_timestamp
#         alias_sym = "#{m}__#{rand}__".to_sym

#         cls.send :alias_method, alias_sym, m
#         cls.class_eval <<-RUBY, __FILE__, __LINE__+1
# def #{m}(*args, &block)
#   self.send #{alias_sym.inspect}, *args, &block
# end
# RUBY
#       }
#     end
  end

end
