module SDGUtils

  # Usage: extend your class with this module.
  module Delegate
    def delegate(*args)
      hash = args.last
      fail "Last arg must be hash" unless Hash === hash
      target = hash[:to]
      fail "No target given; use :to option in the last " +
           "hash parameter to specify the target instance." unless target
      is_proc = (hash.key? :proc) ? hash[:proc] : Proc === target
      mod = Module.new
      args[0..-2].each do |sym|
        sym = sym.to_sym
        proc = if is_proc
          lambda { |*xxx, &block| target.call().send(sym, *xxx, &block) }
        else
          lambda { |*xxx, &block| target.send(sym, *xxx, &block) }
        end
        mod.send :define_method, sym, proc
      end
      if Module === self
        self.send :extend, mod
      else
        (class << self; self end).send :include, mod
      end
    end

    def delegate_all(cls, hash)
      delegate(*cls.instance_methods(false), hash)
    end
  end

  class MetaUtils
    class << self

      # --------------------------------------------------------------
      # Determines full module name of the caller
      # --------------------------------------------------------------
      def caller_module_name
        #|| c[/.*<class:([^>]*)>\'$/, 1]
        caller.map      { |c| c[/.*<module:([^>]*)>\'$/, 1] }
              .find_all { |c| c }
              .reverse
              .join("::")
      end

      # --------------------------------------------------------------
      # Returns the module of the caller by invoking
      # +caller_module_name+ and then converting that string to Class
      # (by calling +SDGUtils::MetaUtils#str_to_class+).
      # --------------------------------------------------------------
      def caller_module
        mn = caller_module_name
        str_to_class(mn) || Object
        # if mn.empty?
          # class << self; self end
        # else
          # str_to_class(mn)
        # end
      end

      # --------------------------------------------------------------
      # Converts String to Class; returns +nil+ if +NameError+
      # --------------------------------------------------------------
      def arry_to_class(arry)
        begin
          arry.inject(Object) do |mod, class_name|
            mod.const_get(class_name)
          end
        rescue NameError
          nil
        end
      end

      def to_class(x)
        case x
        when Class
          x
        else
          str_to_class x.to_s
        end
      end

      def str_to_class(str)
        arry_to_class str.split('::')
      end

      def undef_class(cls)
        split = cls.to_s.split('::')
        mod = arry_to_class split[0..-2]
        if mod
          mod.send :remove_const, split[-1]
        else
          false
        end
      end

      def assign_const(full_name, cst)
        assign_const_in_module(*full_name.split_to_module_and_relative, cst)
      end

      # --------------------------------------------------------------
      # Creates a new constant in module +module_name+ and assigns the
      # +cst+ value to it
      # --------------------------------------------------------------
      def assign_const_in_module(module_or_name, const_base_name, cst)
        raise NameError, "name must not be empty" \
          if const_base_name.nil? || const_base_name.empty?
        raise NameError, "`#{const_base_name}' - name must begin with a capital letter" \
          unless const_base_name[0] =~ /[A-Z]/

        mod = case module_or_name
        when Module
          module_or_name
        when String
          str_to_class(module_or_name)
        else
          Object
        end
        raise NameError, "Module `#{module_or_name}' not found" if mod.nil?
        already_defined = mod.const_defined?(const_base_name.to_sym, false)
        raise NameError, "Constant #{module_or_name}::#{const_base_name} already defined"\
          if already_defined
        mod.const_set(const_base_name.to_sym, cst)
      end

    end
  end

end
