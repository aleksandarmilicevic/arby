require 'alloy/alloy_ast'
require 'sdg_utils/config'
require 'sdg_utils/visitors/visitor'
require 'sdg_utils/print_utils/code_printer'

module Alloy
  module Utils

    class AlloyPrinter
      include Alloy::Ast::Ops

      def self.export_to_als(*what)
        ap = AlloyPrinter.new
        what = Alloy.meta.models if what.empty?
        what.map{|e| ap.send :to_als, e}.join("\n")
        ap.to_s
      end

      def export_to_als(*what)
        old_out = @out
        @out = new_code_printer
        what.map{|e| to_als e}.join("\n")
        ans = @out.to_s
        @out = old_out
        ans
      end

      def to_s
        @out.to_s
      end

      protected

      def initialize(config={})
        @out = new_code_printer
        @conf = SDGUtils::Config.new(nil, {
          :sig_namer => lambda{|sig| sig.relative_name},
          :fun_namer => lambda{|fun| fun.name},
          :arg_namer => lambda{|fld| fld.name}
        }).extend(config)
      end

      def new_code_printer
        SDGUtils::PrintUtils::CodePrinter.new :visitor => self,
                                              :visit_method => :export_to_als
      end

      def to_als(alloy_obj)
        _fail = proc{fail "Unrecognized Alloy entity: #{alloy_obj}:#{alloy_obj.class}"}
        case alloy_obj
        when Alloy::Ast::Model; model_to_als(alloy_obj)
        when Class
          if alloy_obj < Alloy::Ast::ASig
            sig_to_als(alloy_obj)
          else
            _fail[]
          end
        when Alloy::Ast::Fun;          fun_to_als(alloy_obj)
        when Alloy::Ast::Command;      command_to_als(alloy_obj)
        when Alloy::Ast::Field;        field_to_als(alloy_obj)
        when Alloy::Ast::AType;        type_to_als(alloy_obj)
        when Alloy::Ast::Arg;          arg_to_als(alloy_obj)
        when Alloy::Ast::Expr::MExpr;  expr_to_als(alloy_obj)
        when NilClass;                 ""
        else
          _fail[]
        end
      end

      def model_to_als(model)
        @out.pl "module #{model.name}"
        @out.pl
        @out.pn model.sigs, "\n"
        unless model.all_funs.empty?
          @out.pl
          @out.pn model.all_funs, "\n"
        end
        unless model.commands.empty?
          @out.pl
          @out.pn model.commands, "\n"
        end
      end

      def sig_to_als(sig)
        psig = sig.superclass
        abs_str = (mult=sig.meta.multiplicity) ? "#{mult} " : ""
        psig_str = (psig != Alloy::Ast::Sig) ? "extends #{@conf.sig_namer[psig]}" : ""
        sig_name = @conf.sig_namer[sig]
        @out.p "#{abs_str}sig #{sig_name} #{psig_str} {"
        unless sig.meta.fields.empty?
          @out.pl
          @out.in do
            @out.pn sig.meta.fields, ",\n"
          end
          @out.pl
        end
        @out.p "}"
        if sig.meta.facts.empty?
          @out.pl
        else
          @in_appended_facts = true
          @out.pl " {"
          @out.in do
            @out.pn sig.meta.facts.map{|f| f.sym_exe("this").to_conjuncts}.flatten, "\n"
          end
          @out.pl
          @out.pl "}"
          @in_appended_facts = false
        end
        funs = sig.meta.funs + sig.meta.preds
        @out.pl unless funs.empty?
        @out.pn funs, "\n"
      end

      def field_to_als(fld)
        @out.p "#{@conf.arg_namer[fld]}: #{fld.type.to_alloy}"
      end

      def fun_to_als(fun)
        args = if Class === fun.owner && fun.owner.is_sig?
                 selfarg = Alloy::Ast::Arg.new :name => "self", :type => fun.owner
                 [selfarg] + fun.args
               else
                 fun.args
               end
        args_str = args.map(&method(:export_to_als)).join(", ")
        params_str = if args.empty? #&& !fun.fun? && !fun.pred?
                       ""
                     else
                       "[#{args_str}]"
                     end
        ret_str = if fun.fun?
                    ": #{export_to_als fun.ret_type}"
                  else
                    ""
                  end
        kind = if fun.assertion?
                 :assert
               else
                 fun.kind
               end
        fun_name = @conf.fun_namer[fun]
        @out.pl "#{kind} #{fun_name}#{params_str}#{ret_str} {"
        @out.in do
          @out.pn [fun.sym_exe]
        end
        @out.pl "\n}"
      end

      def command_to_als(cmd)
        name = (cmd.name.empty?) ? " " : "#{cmd.name} "
        @out.p "#{cmd.kind} #{name}{"
        if cmd.fun
          @out.pl
          @out.in do
            @out.pn [cmd.fun.sym_exe]
          end
          @out.pl
        end
        @out.pl "} #{cmd.scope}"
      end

      def type_to_als(type)
        case type
        when Alloy::Ast::NoType
          @out.p "univ"
        when Alloy::Ast::UnaryType
          cls = type.klass
          if cls <= Alloy::Ast::ASig
            @out.p @conf.sig_namer[cls]
          else
            @out.p type.cls.to_s.relative_name
          end
        when Alloy::Ast::ProductType
          @out.pn type.lhs
          @out.p " -> "
          @out.p "(" if type.rhs.arity > 1
          @out.pn type.rhs
          @out.p ")" if type.rhs.arity > 1
        when Alloy::Ast::ModType
          @out.p "#{type.mult} "
          @out.p "(" if type.arity > 1
          @out.pn type.type
          @out.p ")" if type.arity > 1
        else
          @out.p type.to_s
        end
      end

      def arg_to_als(arg)
        @out.p "#{arg.name}: #{export_to_als arg.expr}"
      end

      def expr_visitor()
        @expr_visitor ||= SDGUtils::Visitors::TypeDelegatingVisitor.new(self,
          :top_class => Alloy::Ast::Expr::MExpr,
          :visit_meth_namer => proc{|cls, kind| "#{kind}_to_als"}
        )
      end

      def expr_to_als(expr)
        expr_visitor.visit(expr)
      end

      def mexpr_to_als(expr)
        @out.p expr.to_s
      end

      def mvarexpr_to_als(v)
        @out.p v.__name
      end

      def fieldexpr_to_als(fe)
        fld_name = @conf.arg_namer[fe.__field]
        if @in_appended_facts
          @out.p "@#{fld_name}"
        else
          @out.p "#{fld_name}"
        end
      end

      def quantexpr_to_als(expr)
        decl_str = expr.decl.map(&method(:export_to_als)).join(", ")
        expr_kind = case expr.kind
                    when :exist; "some"
                    else expr.kind
                    end
        if expr.comprehension?
          @out.p "{#{decl_str} | "
          @out.pn [expr.body]
          @out.p "}"
        else
          @out.pl "#{expr_kind} #{decl_str} {"
          @out.in do
            @out.pn [expr.body]
          end
          @out.pl "\n}"
        end
      end

      def iteexpr_to_als(ite)
        @out.pl "#{enclose ite.op, ite.cond} implies {"
        @out.in do
          @out.pn [ite.then_expr]
        end
        @out.pl
        @out.p "}"
        unless Alloy::Ast::Expr::BoolConst === ite.else_expr
          @out.pl " else {"
          @out.in do
            @out.pn [ite.else_expr]
          end
          @out.pl
          @out.p "}"
        end
      end

      def sigexpr_to_als(se)
        @out.p @conf.sig_namer[se.__sig]
      end

      def unaryexpr_to_als(ue)
        op_str =
          case ue.op
          when TRANSPOSE, CLOSURE, RCLOSURE; ue.op.to_s
          else "#{ue.op} "
          end
        @out.p "#{op_str}#{enclose ue.op, ue.sub}"
      end

      def binaryexpr_to_als(be)
        op_left, op_right =
          case be.op
          when JOIN;   ["."]
          when SELECT; ["[", "]"]
          else
            [" #{be.op} "]
          end
        @out.p "#{enclose be.op, be.lhs}#{op_left}#{enclose be.op, be.rhs}#{op_right}"
      end

      def callexpr_to_als(ce)
        pre = (ce.has_target?) ? "#{export_to_als ce.target}." : ""
        fun = case f=ce.fun
              when Alloy::Ast::Fun; f.name
              else f
              end
        args = ce.args.map(&method(:export_to_als)).join(", ")
        @out.p "#{pre}#{fun}[#{args}]"
      end

      def boolconst_to_als(bc)
        if bc.value
          ""
        else
          "1 != 0"
        end
      end

      def enclose(op, expr)
        e_str = export_to_als(expr)
        (expr.op.precedence < op.precedence) ? "(#{e_str})" : e_str
      end
    end

  end
end
