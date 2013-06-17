
require 'alloy/alloy_ast.rb'
require 'alloy/alloy_meta.rb'
require 'sdg_utils/meta_utils.rb'

module Alloy
  module DslEngine
  
    # ------------------------------------------
    # == Class +ModelBuilder+
    #
    # Used for creating alloy modules. 
    # ------------------------------------------
    class ModelBuilder
      PARENT_MODULE   = :parent_module
      MODS_TO_INCLUDE = :mods_to_include
      
      @@thread_local = {} # TODO: use some synchronized hash
      
      attr_reader :in_model, :curr_model
      
      #--------------------------------------------------------
      # Returns the singleton instance for the calling thread 
      #--------------------------------------------------------
      def self.get
        tid = 0 #TODO: get thread ID or something
        @@thread_local[tid] ||= self.new        
      end
      
      #--------------------------------------------------------
      # Returns the singleton instance for the calling thread, 
      # after updating its +module_name+ attribute 
      #--------------------------------------------------------
      def self.get_new(options={})
        raise RuntimeError, "Model nesting is not allowed" if @in_model
        mm = self.get
        # update options
        options[PARENT_MODULE] ||= SDGUtils::MetaUtils.caller_module
        options[MODS_TO_INCLUDE] ||= [Alloy::Dsl::Model]
        mm.send(:options=, options)
        mm
      end
      
      #--------------------------------------------------------
      # Returns whether the evaluation is in the context
      # of the Alloy Dsl. 
      #--------------------------------------------------------
      def self.in_dsl_context?
        self.get.in_model
      end
      
      #--------------------------------------------------------
      # Returns the current module, i.e., the module created
      # in the last execution of +alloy_module+.  This is the
      # module in whose scope the body is evaluated.  Only in 
      # the case when no name was provided in the declaration 
      # of this module, all assignments will be fowarded to the
      # parent module, which we call `scope' module.
      #--------------------------------------------------------
      def current_module
        @mod
      end

      #--------------------------------------------------------
      # Returns the current scope module, i.e., the module 
      # in which the created sigs get assigned.  If a non-empty
      # name was provided in the model definition, that the
      # scope module is the same as the current module. 
      #--------------------------------------------------------
      def scope_module
        @scope_mod
      end
      
      #--------------------------------------------------------
      # Creates a modules named +name+ and then executes +&block+
      # using +module_eval+.  All Alloy sigs must be created inside an
      # "alloy model" block.  Inside of this module, all undefined
      # constants are automatically converted to symbols.
      # --------------------------------------------------------
      def model(model_sym, name, &block)
        raise RuntimeError, "Model nesting is not allowed" if @in_model
        @in_model = true
        @curr_model = model_sym
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
          @in_model = false
        end
      end
            
      protected
            
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
      
      # setter for +@options+
      def options=(options)
        @options = options
      end 
      
      # constructors
      def initialize()
        @options = {}
      end      
    end
    
    # -------------------------------------------------------
    # == Class ModBuilder
    # 
    # Used to create expressions like
    #   +one/MyType+, +set/MyType+, etc.
    #
    # An object of this class is returned to represent
    # modifiers like "one", "set", "seq", etc, so that
    # +self/MyType+ and +self.MyType+ can result in an 
    # instance of +Type+
    # -------------------------------------------------------
    class ModBuilder < BasicObject 
      def /(other)
        ModBuilder.mult(@mod_smbl, other)
      end
      
      #------------------------------------------------------------------------
      # Creates an Alloy type with a multiplicity modifier assigned 
      # +Alloy::Ast::ModType+ for a given multiplicity modifier and a given sig.
      #------------------------------------------------------------------------ 
      def self.mult(mod_smbl, *sig)
        if sig.empty?
          new(mod_smbl)
        else
          wrapped = sig[0]
          wrapped = ::Alloy::Ast::UnaryType.new(sig[0]) \
            unless wrapped.kind_of? ::Alloy::Ast::AType
          ::Alloy::Ast::ModType.new(wrapped, mod_smbl)
        end
      end  
      
      private
      
      def initialize(mod_smbl)
        @mod_smbl = mod_smbl
      end            
    end
    
    # -------------------------------------------------------
    # == Class +SigBuilder+
    # 
    # Used to create sig classes.
    # -------------------------------------------------------
    class SigBuilder
      DEFAULT_SUPERCLASS = :default_superclass
      SCOPE_MODULE       = :scope_module
      CREATED_CB         = :created_cb
      
      def initialize(options={})
        options[DEFAULT_SUPERCLASS] ||= Alloy::Ast::Sig
        options[SCOPE_MODULE]       ||= ModelBuilder.get.scope_module
        options[CREATED_CB]           = Array[options[CREATED_CB]].flatten.compact
        @options = options
      end
      
      def self.sig(*args, &block)
        new.sig(*args, &block)
      end
        
      # --------------------------------------------------------------
      # Creates a new class, subclass of either +Alloy::Ast::Sig+ or a
      # user supplied super class, creates a constant with a given
      # +name+ in the callers namespace and assigns the created class
      # to it.
      # --------------------------------------------------------------
      def sig(name, fields={}, &block)
        default_supercls = @options[DEFAULT_SUPERCLASS]
        cls_name, super_cls = case name
        when Class
          [name.relative_name, default_supercls]
        when Array
          raise ArgumentError, "If the first argument is an array, it must have 2 elements, name and super class: Symbol -> Class" unless name.length == 2
          raise ArgumentError,"Specified super class #{name[1]} is not a class but #{name[1].class}" unless name[1].class == Class
          raise Alloy::Ast::TypeError, "Super class (#{name[1]}) must be a subclass of #{default_supercls}" unless name[1] < default_supercls
          [name[0], name[1]]        
        else
          [name, default_supercls] 
        end
        
        full_name = "#{@options[SCOPE_MODULE]}::#{cls_name}"
        cls = Alloy::Ast.create_sig(full_name, super_cls)

        @options[CREATED_CB].each { |cb| cb.call(cls) }        

        cls.fields(fields)

        if block
          ret = cls.class_eval(&block)
          if !ret.nil? && ret.kind_of?(Hash)
            cls.fields(ret) rescue nil
          end        
        end
        
        cls.finish()
        return cls
      end
      
    end
    
  end
end
