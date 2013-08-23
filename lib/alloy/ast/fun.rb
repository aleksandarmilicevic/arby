require 'alloy/ast/expr.rb'
require 'alloy/ast/types'
require 'alloy/ast/type_checker'
require 'alloy/ast/utils'

module Alloy
  module Ast

    # ============================================================================
    # == Class +Fun+
    #
    # Represents function definitions
    #
    # @attr :owner    [ASig, Model]
    # @attr :name     [Symbol]
    # @attr :args     [Array(Arg)]
    # @attr :ret_type [AType]
    # ============================================================================
    class Fun
      include Checks

      attr_reader :kind, :owner, :name, :alloy_method_name, :args, :ret_type, :body

      class << self

        # ~~~~~~~~~~~~~~~~ factory methods ~~~~~~~~~~~~~~~~  #

        def fun(hash)
          Fun.new(:fun, hash)
        end

        def pred(hash)
          hash = ensure_bool_ret(hash.clone)
          Fun.new(:pred, hash)
        end

        def fact(hash)
          hash = ensure_bool_ret(hash.clone)
          hash = ensure_no_args(hash)
          Fun.new :fact, hash
        end

        def assertion(hash)
          hash = ensure_bool_ret(hash.clone)
          hash = ensure_no_args(hash)
          Fun.new :assertion, hash
        end

        def for_method(owner, method_name)
          meth = owner.instance_method(method_name)
          body = meth.bind(Fun.dummy_instance(owner)).to_proc
          fun :name     => method_name,
              :args     => proc_args(meth),
              :ret_type => NoType.new,
              :owner    => owner,
              :body     => body
        end

        # ~~~~~~~~~~~~~~~~ utils ~~~~~~~~~~~~~~~~  #

        # @param cls [Class, Module]
        def dummy_instance(cls)
          if Class === cls
            Alloy::Ast::TypeChecker.check_sig_class(cls)
            cls.send :allocate
          else # it must be a Module
            Alloy::Ast::TypeChecker.check_alloy_module(cls)
            obj = Object.new
            obj.singleton_class.send :include, cls
            obj
          end
        end

        def dummy_instance_expr(cls)
          inst = dummy_instance(cls)
          if Alloy::Ast::ASig === inst
            inst.make_me_sym_expr
          end
          inst
        end

        def proc_args(proc)
          return [] unless proc
          proc.parameters.map{ |mod, sym|
            Alloy::Ast::Arg.new :name => sym,
                                :type => Alloy::Ast::NoType.new
          }
        end

        private

        def ensure_bool_ret(hash)
          rt = hash[:ret_type]
          unless rt.nil? || Alloy::Ast::NoType === rt
            at = Alloy::Ast::AType.get(rt)
            msg = "expected bool return type, got #{at}"
            raise ArgumentError, msg unless (at.isBool? rescue false)
          end
          hash[:ret_type] = :Bool
          hash
        end

        def ensure_no_args(hash)
          args = hash[:args]
          msg = "expected no arguments"
          raise ArgumentError, msg unless args.nil? || args.empty?
          hash[:args] = []
          hash
        end
      end

      private

      def initialize(kind, hash)
        @kind              = kind
        @owner             = hash[:owner]
        @name              = check_iden hash[:name].to_s.to_sym, "function name"
        @alloy_method_name = "#{@name}_alloy"
        @args              = hash[:args] || []
        @ret_type          = Alloy::Ast::AType.get(hash[:ret_type])
        @body              = hash[:body]
      end

      public

      def fun?()       @kind == :fun  end
      def pred?()      @kind == :pred  end
      def fact?()      @kind == :fact  end
      def assertion?() @kind == :assertion  end

      def arity()      args.size end
      def arg_types()  args.map(&:type) end
      def full_type()  (arg_types + [ret_type]).reduce(nil, &ProductType.cstr_proc) end
      def full_name()  "#{owner}.#{name}" end

      def sym_exe
        vars = args.map{|a| Alloy::Ast::Expr::Var.new(a.name, a.type)}
        target = Fun.dummy_instance_expr(@owner)
        target.send alloy_method_name.to_sym, *vars
      end

      def to_opts
        instance_variables.reduce({}) do |acc,sym|
          acc.merge!({sym[1..-1].to_sym => instance_variable_get(sym)})
        end
      end

      def to_s
        args_str = args.map{|a| "#{a.name}: #{a.type}"}.join(", ")
        "#{@kind} #{name} [#{args_str}]: #{ret_type}"
      end
    end

  end
end
