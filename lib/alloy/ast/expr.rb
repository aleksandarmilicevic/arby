require 'alloy/alloy'
require 'alloy/ast/op'
require 'alloy/ast/expr_builder'
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
          target_cls.send :define_method, "#{fname}=" do |val|
            ans = ExprBuilder.apply(Ops::ASSIGN, self.apply_join(fld.to_alloy_expr), val)
            Alloy.boss.add_side_effect(ans)
          end
        end
      end

      def self.ensure_type(expr)
        type = nil
        expr.respond_to?(:__type) and
          type = expr.__type
        if type.nil? || Alloy::Ast::NoType === type
          fail "type not present in expr `#{expr}'"
        end
        type
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

      def self.resolve_expr(e, parent=nil, kind_in_parent=nil, default_val=nil, &else_cb)
        if else_cb.nil?
          else_cb = proc { not_expr_fail(e, parent, kind_in_parent) }
        end
        case e
        when NilClass; default_val || else_cb.call
        when Integer; IntExpr.new(e)
        when MExpr; e
        when AType; TypeExpr.new(e)
        when TrueClass; BoolConst::TRUE
        when FalseClass; BoolConst::FALSE
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

      def self.not_expr_fail(e, parent=nil, kind_in_parent=nil)
        kind = kind_in_parent ? "#{kind_in_parent} " : "#{e}"
        par = parent ? " in #{parent}" : ""
        fail "#{kind} is not an expression#{par}"
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

        attr_reader :__type, :__op
        def __op() @__op || Ops::UNKNOWN end
        def op() __op end #TODO remove

        def __eq(other)  self.__id__ == other.__id__ end
        def __neq(other) !__eq(other) end

        def initialize(type=nil)
          set_type(type)
        end

        def set_type(type=nil)
          @__type = Alloy::Ast::AType.get(type) if type
          Expr.add_methods_for_type(self, @__type, false) if @__type && !@__type.empty?
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

        def is_disjunction() false end
        def is_conjunction() false end

        def to_conjuncts() Expr.to_conjuncts(self) end

        def ==(other)        ExprBuilder.apply(EQUALS, self, other) end
        def !=(other)        ExprBuilder.apply(NOT_EQUALS, self, other) end

        def %(other)         ExprBuilder.apply(REM, self, other) end

        def +(other)         pick_and_apply(IPLUS, PLUS, self, other) end
        def -(other)         pick_and_apply(IMINUS, MINUS, self, other) end
        def /(other)         pick_and_apply(DIV, MINUS, self, other) end
        def **(other)        ExprBuilder.apply(PRODUCT, self, other) end
        def [](other)        ExprBuilder.apply(SELECT, self, other) end
        def <(other)         ExprBuilder.apply(LT, self, other) end
        def <=(other)        ExprBuilder.apply(LTE, self, other) end
        def >(other)         ExprBuilder.apply(GT, self, other) end
        def >=(other)        ExprBuilder.apply(TTE, self, other) end

        def in?(other)       ExprBuilder.apply(IN, self, other) end
        def not_in?(other)   ExprBuilder.apply(NOT_IN, self, other) end
        def contains?(other) ExprBuilder.apply(IN, other, self) end

        def &(other)         ExprBuilder.apply(INTERSECT, self, other) end
        def *(other)         join_closure(RCLOSURE, other) end
        def ^(other)         join_closure(CLOSURE, other) end

        def !()              ExprBuilder.apply(NOT, self) end
        def empty?()         ExprBuilder.apply(NO, self) end
        def no?()            ExprBuilder.apply(NO) end
        def some?()          ExprBuilder.apply(SOME) end
        def lone?()          ExprBuilder.apply(LONE) end
        def one?()           ExprBuilder.apply(ONE) end

        def select(&blk) _blk_to_quant(:comprehension, &blk) end
        def all?(&blk)   _blk_to_quant(:all, &blk) end

        def apply_call(fun, *args) CallExpr.new(self, fun, *args) end
        def apply_join(other)      ExprBuilder.apply(JOIN, self, other) end

        def pick_and_apply(int_op, rel_op, *args)
          op = if args.first.respond_to?(:__type) &&
                   args.first.__type &&
                   args.first.__type.primitive?
                 int_op
               else
                 rel_op
               end
          ExprBuilder.apply(op, *args)
        end

        def join_closure(closure_op, other)
          closure_operand = case other
                            when MExpr; other
                            when String, Symbol;
                              joined = self.send other #returns a "join" BinaryExpr
                              joined.rhs
                            end
          ExprBuilder.apply(JOIN, self, ExprBuilder.apply(closure_op, closure_operand))
        end

        def method_missing(sym, *args, &block)
          return super if Alloy.is_caller_from_alloy?(caller[0])
          if args.empty?
            return super unless Alloy.conf.sym_exe.convert_missing_fields_to_joins
            ExprBuilder.apply(JOIN, self, Var.new(sym))
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

        # @param kind [:all, :some, :comprehension]
        def _blk_to_quant(kind, &blk)
          type = Expr.ensure_type(self)
          msg = "block must have same arity as lhs type: \n" +
                "  block arity: #{blk.arity}\n" +
                "  type arity: #{type.arity} (#{type})"
          fail msg unless blk.arity == type.arity
          domain = self
          if type.unary?
            args = [Alloy::Ast::Arg.new(blk.parameters[0][1], domain)]
            body = blk
          else
            args = type.each_with_index.map{ |col_type, idx|
              Alloy::Ast::Arg.new(blk.parameters[idx][1], col_type)
            }
            body = proc { |*args|
              tuple = ExprBuilder.reduce_to_binary(PRODUCT, *args)
              ExprBuilder.apply(IMPLIES, domain.contains?(tuple), blk.call(*args))
            }
          end
          QuantExpr.send kind, args, body
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
        attr_reader :__name
        def initialize(name, type=nil)
          super(type)
          unless String === name || Symbol === name
            fail "Expected String or Symbol for Var name, got #{name}:#{name.class}"
          end
          @__name = name
        end
        def __op()   Ops::NOOP end
        def to_s() "#{__name}" end
      end

      # ============================================================================
      # == Class +Var+
      #
      # Represents a symbolic variable.
      # ============================================================================
      class Var
        include MVarExpr
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
        def to_s()         @__sig ? @__sig.relative_name : "" end
        def exe_concrete() __sig end
      end

      # ============================================================================
      # == Class +TypeExpr+
      #
      # TODO
      # ============================================================================
      class TypeExpr < Var
        def initialize(type)
          super(type.to_alloy, type)
        end
        def exe_concrete() __type end
      end

      # ============================================================================
      # == Class +IntExpr+
      #
      # TODO
      # ============================================================================
      class IntExpr
        include MExpr
        attr_reader :__value
        def initialize(value)
          #TODO: define some constants in AType for built-in types
          super(Alloy::Ast::AType.get(Integer))
          @__value = value
        end
        def exe_concrete() __value end
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
        attr_reader :children

        def initialize(op, *children)
          @__op = op
          @children = children
        end

        def exe_symbolic
          if children.all?{|ch| MExpr === ch}
            self
          else
            chldrn = children.map{|ch| Expr.resolve_expr(ch, self, "operand")}
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
            ParenExpr.new Expr.resolve_expr(sub)
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

        def __op() (has_target?) ? Ops::JOIN : Ops::SELECT end

        def has_target?() !!target && !(MImplicitInst === target) end

        def exe_symbolic
          if (MExpr === target || target.nil?) && args.all?{|a| MExpr === a}
            self
          else
            t = Expr.resolve_expr(target, self, "target") unless target.nil?
            as = args.map{|a| Expr.resolve_expr(a, self, "argument")}
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
          @__op = Ops::IF_ELSE
        end

        def exe_symbolic
          case
          when MExpr === then_expr && MExpr === else_expr
            self
          else
            te = Expr.resolve_expr(then_expr, self, "then branch", BoolConst::TRUE)
            ee = Expr.resolve_expr(else_expr, self, "else branch", BoolConst::TRUE)
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
      #
      # @attribute decl [Array(Arg)]
      # @attribute body [Proc, MExpr]
      # ============================================================================
      class QuantExpr
        include MExpr
        attr_reader :decl, :body

        def self.all(decl, body)
          self.new(Ops::ALLOF, decl, body)
        end

        def self.exist(decl, body)
          self.new(Ops::SOMEOF, decl, body)
        end

        def self.comprehension(decl, body)
          ans = self.new(Ops::SETCPH, decl, body)
          Expr.add_methods_for_type(ans, decl.last.type)
          ans
        end

        def all?()           op == Ops::ALLOF end
        def exist?()         op == Ops::SOMEOF end
        def comprehension?() op == Ops::SETCPH end

        def kind()   op.sym end
        def arity()  decl.size end

        def exe_symbolic
          case body
          when MExpr; self
          else
            wrapped_body = (Proc === body) ? wrap(body) : body
            b = Expr.resolve_expr(wrapped_body, self, "body", BoolConst::TRUE)
            QuantExpr.new(op, decl, b)
          end
        end

        def to_s
          decl_str = decl.map{|a| "#{a.name}: #{a.expr}"}.join(", ")
          if comprehension?
            "{#{decl_str} | #{body}}"
          else
            "#{kind} #{decl_str} {\n" +
            "  #{body}\n" +
            "}"
          end
        end

        private

        def initialize(op, decl, body)
          @__op, @decl, @body = op, decl, body
          fail unless Qop === @__op
          # fake_body_src = "<failed to extract body source>"
          # @body_src = Alloy::Utils::CodegenRepo.proc_to_src(body) || fake_body_src
        end

        def wrap(proc)
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

