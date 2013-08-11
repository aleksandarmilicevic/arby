require 'sdg_utils/dsl/module_builder'
require 'sdg_utils/meta_utils'

module SDGUtils
  module DSL

    class ClassBuilder
      def initialize(options={})
        @options = {
          :superclass   => ::Object,
          :scope_module => ModuleBuilder.get.scope_module,
          :created_cb   => [],
          :fields_mthd  => :fields,
          :created_mthd => :created,
          :finish_mthd  => :finish
        }.merge!(options)
        @options[:created_cb] = Array[@options[:created_cb]].flatten.compact
      end

      # --------------------------------------------------------------
      # Creates a new class, subclass of `@options[SUPERCLASS]',
      # creates a constant with a given +name+ in the callers
      # namespace and assigns the created class to it.
      # --------------------------------------------------------------
      def build(name, fields={}, &block)
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
        SDGUtils::MetaUtils.assign_const_in_module(@options[:scope_module], cls_name, cls)
        cls_send cls, @options[:created_mthd]
        cls

        @options[:created_cb].each { |cb| cb.call(cls) }

        cls_send cls, @options[:fields_mthd], fields

        if block
          ret = cls.class_eval(&block)
          if !ret.nil? && ret.kind_of?(Hash)
            cls_send cls, @options[:fields_mthd], ret rescue nil #TODO: don't rescue
          end
        end

        cls_send cls, @options[:finish_mthd]
        return cls
      end

      protected

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
