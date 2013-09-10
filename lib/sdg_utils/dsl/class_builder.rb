require 'sdg_utils/delegator'
require 'sdg_utils/meta_utils'
require 'sdg_utils/dsl/base_builder'
require 'sdg_utils/dsl/missing_builder'

module SDGUtils
  module DSL

    #=========================================================================
    # == Class ClassBuilder
    #
    #=========================================================================
    class ClassBuilder < BaseBuilder

      def initialize(options={})
        super({
          :superclass           => ::Object,
          :builder_features     => nil,
          :scope_module         => lambda{mb=ModuleBuilder.get and mb.scope_module},
          :scope_class          => lambda{cb=get_prev and cb.current_class},
          :include_scope_module => true,
          :created_cb           => [],
          :params_mthd          => :__params
        }.merge!(options))
        opts_to_flat_array :created_cb
      end

      def current_class
        @cls
      end

      protected

      # --------------------------------------------------------------
      # If all args are strings or symbols, it creates on class with
      # empty params and empty body for each one of the; otherwise,
      # delegates to +build1+.
      # --------------------------------------------------------------
      def do_build(*args, &body)
        case
        when body.nil? && args.all?{|a| a.respond_to? :to_sym}
          args.map(&method(:do_build1))
        else
          do_build1(*args, &body)
        end
      end

      # --------------------------------------------------------------
      # Creates a new class, subclass of `@conf.superclass',
      # creates a constant with a given +name+ in the callers
      # namespace and assigns the created class to it.
      # --------------------------------------------------------------
      def do_build1(name, params={}, &body)
        supercls = @conf.superclass
        cls_name, super_cls =
          case name
          when MissingBuilder
            missing = name
            missing.consume
            params = missing.args.merge(params)
            body = body || missing.body
            [missing.name, missing.super || supercls]
          when Class, String, Symbol
            # if a class with the same name already exists: ignore for
            # now, use its simple name and later attempt to create a
            # new class with the same name in the current (scope)
            # module.
            [to_clsname(name), supercls]
          when Array
            msg = "If the first argument is an array, it must have " +
                  "2 elements, name and super class: Symbol -> Class"
            raise ArgumentError, msg unless name.length == 2
            msg = "Specified super class #{name[1]} is not a class but #{name[1].class}"
            raise ArgumentError, msg unless name[1].class == Class
            msg = "Super class (#{name[1]}) must be a subclass of #{supercls}"
            raise ArgumentError, msg unless name[1] <= supercls
            [to_clsname(name[0]), name[1]]
          else
            raise ArgumentError, "wrong type of the name argument: #{name}:#{name.class}"
          end
        scope_mod = @conf.scope_module
        scope_cls = @conf.scope_class

        check_superclass(super_cls)

        @cls = Class.new(super_cls)

        if @conf.create_const
          SDGUtils::MetaUtils.assign_const_in_module (scope_cls || scope_mod),
                                                     cls_name,
                                                     @cls
        else
          @cls.instance_eval <<-RUBY, __FILE__, __LINE__+1
            def name() #{cls_name.to_s.inspect} end
          RUBY
        end

        begin
          init(@cls, scope_mod, scope_cls, params, body)
        rescue => e
          # if failed, undef const
          if @conf.create_const
            SDGUtils::MetaUtils.undef_class @cls
          end
          raise e
        end
      end

      private

      def init(cls, scope_mod, scope_cls, params, body)
        if @conf.include_scope_module
          @cls.send(:include, scope_mod) unless Class === scope_mod
        end

        if scope_cls
          @cls.send :include, SDGUtils::MNested
          scope_cls.send :include, SDGUtils::MNestedParent
        end

        # send :created
        safe_send @cls, @conf.created_mthd

        # notify callbacks
        @conf.created_cb.each { |cb| cb.call(@cls) }

        # send :params
        safe_send @cls, @conf.params_mthd, params

        # evaluate body
        if body
          ret = eval_body @cls, :class_eval, &body
          if !ret.nil? && ret.kind_of?(Hash)
            safe_send @cls, @conf.params_mthd, ret
          end
        end

        return @cls
      end

      def to_clsname(name)
        case name
        when Class
          name.to_s.split('::').last
        when MissingBuilder
          mb = name
          mb.consume
          mb.name.to_s
        else
          name.to_sym.to_s
        end
      end

      def check_superclass(super_cls)
        msg = "given super class (#{super_cls}) is not a Class but #{super_cls.class}"
        raise ArgumentError, msg unless Class === super_cls
        base_super = @conf.superclass
        msg = "given super class (#{super_cls}) is not a subclass of #{base_super}"
        raise ArgumentError, msg unless super_cls <= base_super
      end
    end

  end
end
