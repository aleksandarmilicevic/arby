require 'sdg_utils/meta_utils'
require 'sdg_utils/track_nesting'

module SDGUtils
  module DSL

    #=========================================================================
    # == Class ModuleBuilder
    #
    #=========================================================================
    class ModuleBuilder
      PARENT_MODULE   = :parent_module
      MODS_TO_INCLUDE = :mods_to_include

      extend SDGUtils::TrackNesting

      public

      def self.get() top_ctx end

      attr_reader :in_module

      # constructor
      def initialize(options={})
        @options = {
          PARENT_MODULE => SDGUtils::MetaUtils.caller_module
        }.merge!(options)
      end

      #--------------------------------------------------------
      # Returns the current module, i.e., the module created in the
      # last execution of +build+.  This is the module in whose scope
      # the body is evaluated.  Only in the case when no name was
      # provided in the declaration of this module, all assignments
      # will be fowarded to the parent module, which we call the
      # "scope" module.
      # --------------------------------------------------------
      def current_module
        @mod
      end

      #--------------------------------------------------------
      # Returns the current scope module, i.e., the module in which
      # the created sigs get assigned.  If a non-empty name was
      # provided in the module definition, that the scope module is
      # the same as the current module.
      # --------------------------------------------------------
      def scope_module
        @scope_mod
      end

      # --------------------------------------------------------
      # Returns whether the execution is insed the DSL module
      # --------------------------------------------------------
      def in_module?
        @in_module
      end

      #--------------------------------------------------------
      # Creates a module named +name+ and then executes +block+ using
      # +module_eval+.  Inside of this module, all undefined constants
      # are automatically converted to symbols.
      # --------------------------------------------------------
      def build(name, &block)
        ModuleBuilder.push_ctx(self)
        set_in_module()
        begin
          @mod = create_or_get_module(name, @options[MODS_TO_INCLUDE])
          @scope_mod = if name.nil? || name.empty?
                         @options[PARENT_MODULE]
                       else
                         @mod
                       end
          unless block.nil?
            @mod.module_eval(&block)
          end
          return @mod
        ensure
          unset_in_module()
          ModuleBuilder.pop_ctx
        end
      end

      protected

      def set_in_module()   @in_module = true end
      def unset_in_module() @in_module = false end

      def create_module(parent_module, name)
        mod = Module.new
        unless name.nil? || name.empty?
          SDGUtils::MetaUtils.assign_const_in_module(parent_module, name, mod)
        end
        mod
      end

      #-------------------------------------------------------------------
      # Creates a new module and assigns it to a given constant name,
      # or returns an existing one.
      #
      #  * if +name+ is +nil+ or empty, returns the module of +self+
      #  * if constant with named +name+ is already defined,
      #    * if the existing constant is a +Module+, returns that module
      #    * else, raises NameError
      #  * else, creates a new module
      #-------------------------------------------------------------------
      def create_or_get_module(name, mods_to_include)
        parent_module = @options[PARENT_MODULE]
        already_def = parent_module.const_defined?(name, false) rescue false
        ret_module = (parent_module.const_get name if already_def) ||
                     create_module(parent_module, name)

        raise NameError, "Constant #{name} already defined in module #{parent_module}"\
          unless ret_module.class == Module

        mods_to_include.each {|m|
          ret_module.send(:include, m) unless ret_module.include? m
          ret_module.send(:extend, m)
        } unless ret_module == Object

        ret_module
      end

    end

  end
end
