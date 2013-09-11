require 'alloy/alloy'
require 'alloy/ast/op'
require 'alloy/ast/field'
require 'alloy/ast/types'
require 'alloy/utils/codegen_repo'
require 'alloy/utils/expr_visitor'

module Alloy
  module Ast
    module Expr

      def self.as_atom(sig_inst, name)
        cls = sig_inst.singleton_class
        cls.send :include, Alloy::Ast::Expr::MAtomToExpr
        cls.class_eval <<-RUBY, __FILE__, __LINE__+1
          def name() #{name.inspect} end
          def type() @atype ||= Alloy::Ast::AType.get(#{sig_inst.class.inspect}) end
        RUBY
      end

      def self.add_field_methods_for_type(target_inst, type, define_type_method=true)
        cls = target_inst.singleton_class
        cls.send :define_method, :type, lambda{type} if define_type_method
        range_cls = type.range.klass
        if Class === range_cls && range_cls < Alloy::Ast::ASig
          flds = range_cls.meta.fields_including_sub_and_super
          add_field_methods(cls, flds)
        end
      end

      def self.add_field_methods(target_cls, fields, eval_meth=:class_eval)
        fields.each do |fld|
          target_cls.send :define_method, "#{Field.getter_sym(fld)}" do
            self.apply_join fld.to_alloy_expr
          end
          #TODO setter?
        end
      end

      def self.replace_subexpressions(e, orig, replacement)
        rbilder = Alloy::Utils::ExprRebuilder.new do |expr|
          (expr.__id__ == orig.__id__) ? replacement : nil
        end
        rbilder.rebuild(e)
      end

      # ============================================================================
      # == Module +MExpr+
      #
      # Represents an Alloy expression that is upon creation always
      # "executed" either concretely or symbolically (not all
      # expressions support both execution modes.
      # ============================================================================
      module MExpr
        def self.included(base)
          base.class_eval <<-RUBY, __FILE__, __LINE__+1
          def self.new(*args, &block)
            expr = allocate
            expr.send :initialize, *args, &block
            expr.exe
          end
          RUBY
        end

        def exe
          case
          when Alloy.symbolic_mode?; exe_symbolic
          when Alloy.concrete_mode?; exe_concrete
          else fail "unknown mode: #{mode}"
          end
        end

        def exe_symbolic() self end
        def exe_concrete() self end

        def ==(other)  apply_op("equals", other) end
        def !=(other)  apply_op("not_equals", other) end
        def +(other)   apply_op("plus", other) end
        def -(other)   apply_op("minus", other) end
        def /(other)   apply_op("div", other) end
        def %(other)   apply_op("rem", other) end
        def *(other)
          if self.respond_to?(:type) && self.type.primitive?
            apply_op("mul", other)
          else
            apply_op("product", other)
          end
        end
        def <(other)   apply_op("lt", other) end
        def <=(other)  apply_op("lte", other) end
        def >(other)   apply_op("gt", other) end
        def >=(other)  apply_op("gte", other) end
        def in?(other) apply_op("in", other) end

        def !()        apply_op("not") end

        def empty?()   apply_op("no") end
        def no?()      apply_op("no") end
        def some?()    apply_op("some") end
        def lone?()    apply_op("lone") end
        def one?()     apply_op("one") end



        def apply_ite(cond, then_expr, else_expr)
          ITEExpr.new(cond, then_expr, else_expr)
        end

        def apply_call(fun, *args) CallExpr.new self, fun, *args end
        def apply_join(other)      apply_op("join", other) {|l,r| l.join(r)} end

        def apply_op(op_name, *args, &type_proc)
          ans = if args.empty?
                  UnaryExpr.send op_name.to_sym, self
                elsif args.size == 1
                  BinaryExpr.send op_name.to_sym, self, args[0]
                else
                  op_args = [self] + args
                  NaryExpr.send op_name.to_sym, *op_args
                end
          all_args = [self] + args
          if type_proc && all_args.all?{|a| a.respond_to?(:type)}
            all_types = all_args.map(&:type)
            if all_types.none?(&:nil?)
              result_type = type_proc.call(all_types)
              Expr.add_field_methods_for_type(ans, result_type)
            end
          end
          ans
        end

        def method_missing(sym, *args, &block)
          return super if Alloy.is_caller_from_alloy?(caller[0])
          if args.empty?
            return super unless Alloy.conf.sym_exe.convert_missing_fields_to_joins
            apply_join Var.new(sym)
          else
            return super unless Alloy.conf.sym_exe.convert_missing_methods_to_fun_calls
            if sym == :[] && args.size == 1
              lhs = (MExpr === args[0]) ? args[0] : Var.new(args[0])
              lhs.apply_join ParenExpr.new(self)
            else
              #TODO do something when `sym == :[]' and args.size > 1:
              #     either fail or convert into multistep join
              apply_call sym, *args
            end
          end
        end

        def to_str
          to_s
        end

        protected

        def resolve_expr(e, parent=nil, kind_in_parent=nil, default_val=nil, &else_cb)
          if else_cb.nil?
            else_cb = proc { not_expr_fail(e, parent, kind_in_parent) }
          end
          case e
          when NilClass; default_val || else_cb.call
          when MExpr; e
          when Proc; resolve_expr(e.call, parent, kind_in_parent, default_val, &else_cb)
          else
            if e.respond_to? :to_alloy_expr
              al_expr = e.send :to_alloy_expr
              resolve_expr(al_expr, parent, kind_in_parent, default_val, &else_cb)
            else
              else_cb.call
            end
          end
        end

        def not_expr_fail(e, parent=nil, kind_in_parent=nil)
          kind = kind_in_parent ? "#{kind_in_parent} " : "#{e}"
          par = parent ? " in #{parent}" : ""
          fail "#{kind} is not an expression#{par}"
        end
      end


      # ============================================================================
      # == Class +BoolConst+
      #
      # Represents a boolean constant.
      # ============================================================================
      class BoolConst
        include MExpr
        attr_reader :value

        private

        def initialize(val)
          @value = val
        end

        public

        TRUE  = BoolConst.new(true)
        FALSE = BoolConst.new(false)

        # def self.True()  TRUE end
        # def self.False() FALSE end
        def self.True?(ex)          is_obj_equal(TRUE, ex) end
        def self.False?(ex)         is_obj_equal(FALSE, ex) end
        def self.Const?(ex)         True?(ex) || False?(ex) end
        def self.is_obj_equal(l, r) l.__id__ == r.__id__ end

        def to_s
          "#{value}"
        end
      end

      # ============================================================================
      # == Module +MVarExpr+
      #
      # Represents a symbolic variable.
      # ============================================================================
      module MVarExpr
        include MExpr
        attr_reader :name, :type
        def to_s() "#{name}" end
      end

      # ============================================================================
      # == Class +Var+
      #
      # Represents a symbolic variable.
      # ============================================================================
      class Var
        include MVarExpr
        def initialize(name, type=nil)
          unless String === name || Symbol === name
            fail "Expected String or Symbol for Var name, got #{name}:#{name.class}"
          end
          type = Alloy::Ast::AType.get(type) if type
          @name, @type = name, type
          Expr.add_field_methods_for_type(self, type, false) if type
        end
      end

      # ============================================================================
      # == Class +FieldExpr+
      #
      # TODO
      # ============================================================================
      class FieldExpr < Var
        attr_reader :field
        def initialize(fld)
          @field = fld
          super(fld.name, fld.full_type)
        end
        def exe_concrete() field end
      end

      # ============================================================================
      # == Class +SigExpr+
      #
      # TODO
      # ============================================================================
      class SigExpr < Var
        attr_reader :sig
        def initialize(sig)
          super(sig.relative_name, Alloy::Ast::AType.get(sig))
          @sig = sig
        end
        def to_s() @sig.relative_name end
        def exe_concrete() sig end
      end

      # ============================================================================
      # == Module +MAtomToExpr+
      #
      # TODO
      # ============================================================================
      module MAtomToExpr
        include MVarExpr

        def self.included(sig_cls)
          Expr.add_field_methods(sig_cls, sig_cls.meta.fields)
        end

        def method_missing(sym, *args, &block)
          if p=__parent()
            p.send sym, *args, &block
          else
            raise ::NameError, "method #{sym} not found in #{self}:#{self.class}"
          end
        end

        def to_s() name end
      end

      # ============================================================================
      # == Class +NaryExpr+
      #
      # Represents an n-ary expression.
      # ============================================================================
      class NaryExpr
        include MExpr
        attr_reader :op, :children

        def initialize(op, *children)
          @op = op
          @children = children
        end

        def exe_symbolic
          if children.all?{|ch| MExpr === ch}
            self
          else
            chldrn = children.map{|ch| resolve_expr(ch, self, "operand")}
            self.class.new op, *chldrn
          end
        end

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

      # ============================================================================
      # == Class +UnaryExpr+
      #
      # Represents a unary expression.
      # ============================================================================
      class UnaryExpr < NaryExpr
        def initialize(op, sub) super(op, sub) end
        def sub()               children.first end

        add_constructors_for_ops Alloy::Ast::UnaryOps.all

        def to_s
          "(#{op} #{sub})"
        end
      end

      # ============================================================================
      # == Class +ParenExpr+
      #
      # Represents an expression enclosed in parens.
      # ============================================================================
      class ParenExpr
        include MExpr

        attr_reader :sub
        def initialize(sub) @sub = sub end

        def exe_symbolic
          if MExpr === sub
            self
          else
            ParenExpr.new resolve_expr(sub)
          end
        end

        def to_s() "(#{sub})" end
      end

      # ============================================================================
      # == Class +BinaryExpr+
      #
      # Represents a binary expression.
      # ============================================================================
      class BinaryExpr < NaryExpr
        def initialize(op, lhs, rhs) super(op, lhs, rhs) end
        def lhs()                    children[0] end
        def rhs()                    children[1] end

        add_constructors_for_ops Alloy::Ast::BinaryOps.all

        def to_s
          op_str = op.to_s
          op_str = " #{op_str} " unless op_str == "."
          "#{lhs}#{op_str}#{rhs}"
        end
      end

      # ============================================================================
      # == Class +CallExpr+
      #
      # Represents a function call.
      # ============================================================================
      class CallExpr
        include MExpr
        attr_reader :target, :fun, :args

        def initialize(target, fun, *args)
          @target, @fun, @args = target, fun, args
        end

        def exe_symbolic
          if MExpr === target && args.all?{|a| MExpr === a}
            self
          else
            t = resolve_expr(target, self, "target")
            as = args.map{|a| resolve_expr(a, self, "argument")}
            self.class.new t, fun, *as
          end
        end

        def to_s
          pre = target ? "#{target}." : ""
          "#{pre}#{fun}[#{args.join(', ')}]"
        end
      end

      # ============================================================================
      # == Class +ITEExpr+
      #
      # Represents an "if-then-else" expression.
      # ============================================================================
      class ITEExpr
        include MExpr
        attr_reader :cond, :then_expr, :else_expr
        def initialize(cond, then_expr, else_expr)
          @cond, @then_expr, @else_expr = cond, then_expr, else_expr
        end

        def exe_symbolic
          case
          when MExpr === then_expr && MExpr === else_expr
            self
          else
            te = resolve_expr(then_expr, self, "then branch", BoolConst::TRUE)
            ee = resolve_expr(else_expr, self, "else branch", BoolConst::TRUE)
            ITEExpr.new(cond, te, ee)
          end
        end

        def to_s
"""
  (#{cond}) implies {
    #{then_expr}
  } else {
    #{else_expr}
  }
"""
        end
      end

      # ============================================================================
      # == Class +QuantExpr+
      #
      # Represents a first-order quantifier expression.
      # ============================================================================
      class QuantExpr
        include MExpr
        attr_reader :kind, :decl, :body

        def self.all(decl, body)
          self.new(:all, decl, body)
        end

        def self.exist(decl, body)
          self.new(:exist, decl, body)
        end

        def all?()   @kind == :all end
        def exist?() @kind == :exist end

        def exe_symbolic
          case body
          when MExpr; self
          else
            wrapped_body = (Proc === body) ? wrap(body) : body
            b = resolve_expr(wrapped_body, self, "body", BoolConst::TRUE)
            QuantExpr.new(kind, decl, b)
          end
        end

        def to_s
          decl_str = decl.map{|k,v| "#{k}: #{v}"}.join(", ")
          "#{@kind} #{decl_str} {\n" +
          "  #{body}\n" +
          "}"
        end

        private

        def initialize(kind, decl, body)
          @kind, @decl, @body = kind, decl, body
          # fake_body_src = "<failed to extract body source>"
          # @body_src = Alloy::Utils::CodegenRepo.proc_to_src(body) || fake_body_src
        end

        def wrap(proc)
          proc_self = proc.binding.eval "self"
          vars = decl.reduce({}) do |acc, arg|
            acc[arg.name] = Var.new(arg.name, arg.type)
            acc
          end
          proc {
            SDGUtils::ShadowMethods.shadow_methods_while(vars, &proc)
          }
        end
      end

    end
  end
end

