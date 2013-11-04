module SDGUtils

  # Usage: include this module in your class
  module ShadowMethods
    extend self

    def shadow_methods_while(hash, ctx=nil, &block)
      ctx ||= block.binding.eval "self"
      hash.each do |mth_name, ret_val|
        ctx.define_singleton_method mth_name.to_sym, lambda{ret_val}
      end
      begin
        if block.arity == -1
          block.call *hash.values
        else
          block.call *hash.values[0...(block.arity)]
        end
      ensure
        hash.each do |mth_name, _|
          ctx.define_singleton_method mth_name.to_sym do super() end
        end
      end
    end
  end

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

      def check_identifier(str)
        return nil unless str
        # ok = ::Object.new.send(:define_singleton_method, str, lambda{}) rescue false
        # ok = ::Object.new.instance_eval "def #{str}() end; true" rescue false
        ok = !!(str =~ /^[a-z_][a-zA-Z_0-9]*\??$/)
        ok ? str : nil
      end

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
        str_to_class(mn) || ::Object
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
          arry.inject(::Object) do |mod, class_name|
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
        return unless cls.name
        split = cls.name.split('::')
        mod = arry_to_class split[0..-2]
        if mod
          mod.send :remove_const, split[-1]
        else
          false
        end
      end

      def split_to_module_and_relative(name)
        sp = name.split('::')
        [sp[0..-2].join('::'), sp.last]
      end

      def assign_const(full_name, cst)
        mod_name, cls_name =
          if full_name[-2..-1] == "::"
            [full_name[0...-2], ""]
          else
            split_to_module_and_relative(full_name)
          end
        assign_const_in_module(mod_name, cls_name, cst)
      end

      # --------------------------------------------------------------
      # Creates a new constant in module +module_name+ and assigns the
      # +cst+ value to it
      # --------------------------------------------------------------
      def assign_const_in_module(module_or_name, const_base_name, cst)
        const_base_name = const_base_name.to_s
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
                ::Object
              end
        raise NameError, "Module `#{module_or_name}' not found" if mod.nil?
        already_defined = mod.const_defined?(const_base_name.to_sym, false)
        if already_defined
          msg = "Constant #{module_or_name}::#{const_base_name} already defined"
          raise NameError, msg
        end
        mod.const_set(const_base_name.to_sym, cst)
      end

      def undef_const_from(mod, const_base_name)
        mod.send :remove_const, const_base_name
      end

    end
  end

end
