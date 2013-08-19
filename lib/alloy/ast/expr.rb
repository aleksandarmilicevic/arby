require 'alloy/ast/op'
require 'sdg_utils/lambda/sourcerer'

module Alloy
  module Ast

    module MExpr
      def ==(other) apply_op("equals", other) end
      def !=(other) apply_op("not_equals", other) end
      def +(other)  apply_op("plus", other) end
      def -(other)  apply_op("minus", other) end
      def /(other)  apply_op("div", other) end
      def %(other)  apply_op("rem", other) end
      def *(other)  apply_op("mul", other) end
      def <(other)  apply_op("lt", other) end
      def <=(other) apply_op("lte", other) end
      def >(other)  apply_op("gt", other) end
      def >=(other) apply_op("gte", other) end

      def apply_ite(cond, then_expr, else_expr)
        ITEExpr.new(cond, then_expr, else_expr)
      end

      def apply_call(fun, *args) CallExpr.new sym, *args end

      def apply_op(op_name, *args)
        if args.empty?
          UnaryExpr.send op_name.to_sym, self
        elsif args.size == 1
          BinaryExpr.send op_name.to_sym, self, args[0]
        else
          op_args = [self] + args
          NaryExpr.send op_name.to_sym, *op_args
        end
      end

      def method_missing(sym, *args, &block)
        if args.empty?
          apply_op "join", Var.new(sym)
        else
          apply_call sym, *args
        end
      end
    end

    class Var
      include MExpr
      attr_reader :name, :type
      def initialize(name, type=nil) @name, @type = name, type end
    end

    class NaryExpr
      include MExpr
      attr_reader :op, :children
      def initialize(op, *children) @op, @children = op, children end

      protected

      def self.add_constructors_for_ops(ops)
        ops.each do |op|
          class_eval <<-RUBY, __FILE__, __LINE__+1
          def self.#{op.name}(*args)
            self.new(Alloy::Ast::Op.by_name(#{op.name.inspect}), *args)
           end
          RUBY
        end
      end
    end

    class UnaryExpr < NaryExpr
      def initialize(op, sub) super(op, sub) end
      def sub()               children.first end

      add_constructors_for_ops Alloy::Ast::UnaryOps.all
    end

    class BinaryExpr < NaryExpr
      def initialize(op, lhs, rhs) super(op, lhs, rhs) end
      def lhs()                    children[0] end
      def rhs()                    children[1] end

      add_constructors_for_ops Alloy::Ast::BinaryOps.all
    end

    class CallExpr
      include MExpr
      attr_reader :fun, :args
      def initialize(fun, *args) @fun, @args = fun, args end
    end

    class ITEExpr
      include MExpr
      attr_reader :cond, :then_exp, :else_expr
      def initialize(cond, then_expr, else_expr)
        @cond, @then_expr, @else_expr = cond, then_expr, else_expr
      end
    end

    class QuantExpr
      include MExpr
      attr_reader :kind, :decl, :body

      def self.all(decl, &block)
        self.new(:all, decl, &block)
      end

      def self.exist(decl, &block)
        self.new(:exist, decl, &block)
      end

      def all?()   @kind == :all end
      def exist?() @kind == :exist end

      def to_s
        decl_str = decl.map{|k,v| "#{k}: #{v}"}.join(", ")
        "#{@kind} #{decl_str} {\n" +
        "  #{@body_src}\n" +
        "}"
      end

      private

      def initialize(kind, decl, &body)
        @kind, @decl, @body = kind, decl, body
        fake_body_src = "<failed to extract body source>"
        @body_src = SDGUtils::Lambda::Sourcerer.proc_to_src(body) rescue fake_body_src
      end

    end
  end
end
