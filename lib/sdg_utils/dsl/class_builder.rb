require 'sdg_utils/meta_utils'
require 'sdg_utils/dsl/base_builder'

module SDGUtils
  module DSL

    #=========================================================================
    # == Class ClassBuilder
    #
    #=========================================================================
    class ClassBuilder < BaseBuilder

      #TODO rewrite using SDGUtils::Config

      def initialize(options={})
        @options = {
          :superclass       => ::Object,
          :builder_features => nil,
          :scope_module     => ModuleBuilder.get.scope_module,
          :created_cb       => [],
          :created_mthd     => :__created,
          :params_mthd      => :__params,
          :finish_mthd      => :__finish,
          :eval_body_mthd   => :__eval_body,
        }.merge!(options)
        @options[:created_cb] = Array[@options[:created_cb]].flatten.compact
      end

      # --------------------------------------------------------------
      # If all args are strings or symbols, it creates on class with
      # empty fields and empty body for each one of the; otherwise,
      # delegates to +build1+.
      # --------------------------------------------------------------
      def build(*args, &body)
        BaseBuilder.push_ctx(self)
        set_in_class()
        begin
          case
          when body.nil? && args.all?{|a| String === a || Symbol === a}
            args.each &method(:build1).to_proc
          else
            build1(*args, &body)
          end
        ensure
          unset_in_class()
          BaseBuilder.pop_ctx
        end
      end

      def in_body?()  @in_body end
      def in_class?() @in_class end

      protected

      def set_in_class()   @in_class = true  end
      def unset_in_class() @in_class = false end

      # --------------------------------------------------------------
      # Creates a new class, subclass of `@options[SUPERCLASS]',
      # creates a constant with a given +name+ in the callers
      # namespace and assigns the created class to it.
      # --------------------------------------------------------------
      def build1(name, fields={}, &body)
        supercls = @options[:superclass]
        cls_name, super_cls =
          case name
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

        cls = Class.new(super_cls)

        # send :created
        cls_send cls, @options[:created_mthd]

        # notify callbacks
        @options[:created_cb].each { |cb| cb.call(cls) }

        # send :fields
        cls_send cls, @options[:params_mthd], fields

        # evaluate body
        if body
          # bld_feat = @options[:builder_features] and cls.extend(bld_feat)
          ebm = @options[:eval_body_mthd]
          eval_body_mthd_name = cls.respond_to?(ebm) ? ebm : "class_eval"
          ret = begin
                  @in_body = true
                  cls.send eval_body_mthd_name, &body
                ensure
                  @in_body = false
                end
          if !ret.nil? && ret.kind_of?(Hash)
            cls_send cls, @options[:fields_mthd], ret
          end
        end

        # send :finish
        cls_send cls, @options[:finish_mthd]

        SDGUtils::MetaUtils.assign_const_in_module @options[:scope_module], cls_name, cls
        return cls
      end

      def cls_send(cls, sym, *args)
        cls.send sym, *args if cls.respond_to? sym
      end

      def to_clsname(name)
        case name
        when Class
          name.to_s.split('::').last
        else
          name.to_s
        end
      end
    end

  end
end
