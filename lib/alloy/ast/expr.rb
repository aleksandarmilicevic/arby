require 'alloy/alloy'
require 'alloy/ast/op'
require 'alloy/ast/field'
require 'alloy/ast/types'
require 'alloy/utils/codegen_repo'
require 'alloy/utils/expr_visitor'

module Alloy
  module Ast
    module Expr

      def self.as_atom(sig_inst, name, type=sig_inst.class, expr_mod=MAtomExpr)
        cls = sig_inst.singleton_class
        cls.send :include, expr_mod
        cls.class_eval <<-RUBY, __FILE__, __LINE__+1
          def __name() #{name.inspect} end
          def __type() @__atype ||= Alloy::Ast::AType.get(#{type.inspect}) end
        RUBY
        Expr.add_methods_for_type(sig_inst, AType.get(type), false)
      end

      def self.add_methods_for_type(target_inst, type, define_type_method=true)
        cls = target_inst.singleton_class
        cls.send :define_method, :__type, lambda{type} if define_type_method
        range_cls = type.range.klass
        if (Alloy::Ast::ASig >= range_cls rescue false)
          add_field_methods cls, range_cls.meta.fields_including_sub_and_super
          add_field_methods cls, range_cls.meta.inv_fields_including_sub_and_super
          add_fun_methods   cls, range_cls.meta.all_funs
        elsif (Alloy::Dsl::ModelDslApi >= range_cls rescue false)
          add_fun_methods   cls, range_cls.meta.all_funs
        end
      end

      def self.add_fun_methods(target_cls, funs)
        funs.each do |fun|
          target_cls.send :define_method, fun.name.to_sym do |*args|
            self.apply_call fun, *args
          end
        end
      end

      def self.add_field_methods(target_cls, fields)
        fields.each do |fld|
          fname = if fld.is_inv?
                    "#{fld.inv.getter_sym}!"
                  else
                    fld.getter_sym.to_s
                  end
          target_cls.send :define_method, "#{fname}" do
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

      def self.to_conjuncts(e)
        if BinaryExpr === e && e.op == Ops::AND
          to_conjuncts(e.lhs) + to_conjuncts(e.rhs)
        else
          [e]
        end
      end

      # ============================================================================
      # == Module +MExpr+
      #
      # Represents an Alloy expression that is upon creation always
      # "executed" either concretely or symbolically (not all
      # expressions support both execution modes.
      # ============================================================================
      module MExpr
        include Ops

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

        def op() Ops::UNKNOWN end

        def is_disjunction() false end
        def is_conjunction() false end

        def to_conjuncts() Expr.to_conjuncts(self) end

        def ==(other)        apply_op(EQUALS, other) end
        def !=(other)        apply_op(NOT_EQUALS, other) end
        def %(other)         apply_op(REM, other) end
        def +(other)         apply_int_or_rel_op(IPLUS, PLUS, other) end
        def -(other)         apply_int_or_rel_op(IMINUS, MINUS, other) end
        def /(other)         apply_int_or_rel_op(DIV, MINUS, other) end
        def **(other)        apply_op(PRODUCT, other) end
        def [](other)        apply_op("select", other) end
        def <(other)         apply_op("lt", other) end
        def <=(other)        apply_op("lte", other) end
        def >(other)         apply_op("gt", other) end
        def >=(other)        apply_op("gte", other) end
        def in?(other)       apply_op("in", other) end
        def not_in?(other)   apply_op("not_in", other) end
        def contains?(other) resolve_expr(other).apply_op("in", self) end
        def &(other)         apply_op("intersect", other) end
        def *(other)
          apply_int_or_rel_op(MUL, proc{
            join_rhs =
              case other
              when MExpr; other
              when String, Symbol;
                joined = self.send other #returns a "join" BinaryExpr
                joined.rhs
              end
            apply_join(join_rhs.apply_op("rclosure"))
          }, other)
        end
        def ^(other)
          #TODO: DRY
          join_rhs =
            case other
            when MExpr; other
            when String, Symbol;
              joined = self.send other #returns a "join" BinaryExpr
              joined.rhs
            end
          apply_join(join_rhs.apply_op("closure"))
        end
        def !()        apply_op("not") end

        def empty?()   apply_op("no") end
        def no?()      apply_op("no") end
        def some?()    apply_op("some") end
        def lone?()    apply_op("lone") end
        def one?()     apply_op("one") end

        def apply_ite(cond, then_expr, else_expr)
          ITEExpr.new(cond, then_expr, else_expr)
        end

        def apply_call(fun, *args) CallExpr.new(self, fun, *args) end
        def apply_join(other)      apply_op("join", other) {|l,r| l.join(r)} end

        def apply_int_or_rel_op(int_op, rel_op, *args, &type_proc)
          op =
            if args.first.respond_to?(:__type) && args.first.__type.primitive?
              int_op
            else
              rel_op
            end
          Proc === op ? op.call : apply_op(rel_op, *args, &type_proc)
        end

        def apply_op(op_name, *args, &type_proc)
          op_name = case op_name
                    when Op; op_name.name
                    else op_name.to_s
                    end
          # Op.by_name(op_name).apply(*args)
          ans = if args.empty?
                  UnaryExpr.send op_name.to_sym, self
                elsif args.size == 1
                  BinaryExpr.send op_name.to_sym, self, args[0]
                else
                  op_args = [self] + args
                  NaryExpr.send op_name.to_sym, *op_args
                end
          all_args = [self] + args
          if type_proc && all_args.all?{|a| a.respond_to?(:__type)}
            all_types = all_args.map(&:__type)
            if all_types.none?(&:nil?)
              result_type = type_proc.call(all_types)
              Expr.add_methods_for_type(ans, result_type)
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
            apply_call sym, *args
            # if sym == :[] && args.size == 1
            #   lhs = (MExpr === args[0]) ? args[0] : Var.new(args[0])
            #   lhs.apply_join ParenExpr.new(self)
            # else
            #   #TODO do something when `sym == :[]' and args.size > 1:
            #   #     either fail or convert into multistep join
            #   apply_call sym, *args
            # end
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
        attr_reader :__name, :__type
        def op() Ops::NOOP end
        def to_s() "#{__name}" end
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
          @__name, @__type = name, type
          Expr.add_methods_for_type(self, type, false) if type
        end
      end

      # ============================================================================
      # == Class +FieldExpr+
      #
      # TODO
      # ============================================================================
      class FieldExpr < Var
        attr_reader :__field
        def initialize(fld)
          @__field = fld
          super(fld.name, fld.full_type)
        end
        def to_s() __field.name end
        def exe_concrete() __field end
      end

      # ============================================================================
      # == Class +SigExpr+
      #
      # TODO
      # ============================================================================
      class SigExpr < Var
        attr_reader :__sig
        def initialize(sig)
          super(sig.relative_name, Alloy::Ast::AType.get(sig))
          @__sig = sig
        end
        def to_s() @__sig ? @__sig.relative_name : "" end
        def exe_concrete() __sig end
      end

      # ============================================================================
      # == Module +MAtom+
      #
      # TODO
      # ============================================================================
      module MAtomExpr
        include MVarExpr

        def method_missing(sym, *args, &block)
          if p=__parent()
            p.send sym, *args, &block
          else
            raise ::NameError, "method `#{sym}' not found in #{self}:#{self.class}"
          end
        end

        def to_s() @__name end
      end

      # ============================================================================
      # == Module +MAtomExpr+
      #
      # TODO
      # ============================================================================
      module MImplicitInst
        include MAtomExpr
        def apply_join(other) other end
        def to_s() "super" end
      end

      # ============================================================================
      # == Class +NaryExpr+
      #
      # Represents an n-ary expression.
      # ============================================================================
      class NaryExpr
        include MExpr
        # TODO: rename refactor... 
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

        def is_disjunction() op == Ops::OR end
        def is_conjunction() op == Ops::AND end

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

        add_constructors_for_ops Alloy::Ast::Op.by_arity(1)

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

        add_constructors_for_ops Alloy::Ast::Op.by_arity(2)

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

        def op() (has_target?) ? Ops::JOIN : Ops::SELECT end

        def has_target?() !!target && !(MImplicitInst === target) end

        def exe_symbolic
          if (MExpr === target || target.nil?) && args.all?{|a| MExpr === a}
            self
          else
            t = resolve_expr(target, self, "target") unless target.nil?
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
        attr_reader :cond, :then_expr, :else_expr, :op
        def initialize(cond, then_expr, else_expr)
          @cond, @then_expr, @else_expr = cond, then_expr, else_expr
          @op = Ops::IF_ELSE
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
        attr_reader :op, :decl, :body

        def self.all(decl, body)
          self.new(Ops::ALLOF, decl, body)
        end

        def self.exist(decl, body)
          self.new(Ops::SOMEOF, decl, body)
        end

        def all?()   op == Ops::ALLOF end
        def exist?() op == Ops::SOMEOF end

        def kind()   op.sym end

        def exe_symbolic
          case body
          when MExpr; self
          else
            wrapped_body = (Proc === body) ? wrap(body) : body
            b = resolve_expr(wrapped_body, self, "body", BoolConst::TRUE)
            QuantExpr.new(op, decl, b)
          end
        end

        def to_s
          decl_str = decl.map{|k,v| "#{k}: #{v}"}.join(", ")
          "#{kind} #{decl_str} {\n" +
          "  #{body}\n" +
          "}"
        end

        private

        def initialize(op, decl, body)
          @op, @decl, @body = op, decl, body
          fail unless Qop === @op
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

