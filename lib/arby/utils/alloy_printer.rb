require 'arby/arby_ast'
require 'sdg_utils/config'
require 'sdg_utils/visitors/visitor'
require 'sdg_utils/print_utils/code_printer'

module Arby
  module Utils

    class AlloyPrinter
      include Arby::Ast::Ops

      def self.export_to_als(*what)
        ap = AlloyPrinter.new
        what = Arby.meta.models if what.empty?
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

      def to_als(arby_obj)
        _fail = proc{fail "Unrecognized Arby entity: #{alloy_obj}:#{alloy_obj.class}"}
        case arby_obj
        when Arby::Ast::Model; model_to_als(arby_obj)
        when Class
          if arby_obj < Arby::Ast::ASig
            sig_to_als(arby_obj)
          else
            _fail[]
          end
        when Arby::Ast::Fun;          fun_to_als(arby_obj)
        when Arby::Ast::Command;      command_to_als(arby_obj)
        when Arby::Ast::Field;        field_to_als(arby_obj)
        when Arby::Ast::AType;        type_to_als(arby_obj)
        when Arby::Ast::Arg;          arg_to_als(arby_obj)
        when Arby::Ast::Expr::MExpr;  expr_to_als(arby_obj)
        when NilClass;                ""
        else
          _fail[]
        end
      end

      def model_to_als(model)
        @out.pl "module #{model.relative_name}"
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
        psig_str = (psig != Arby::Ast::Sig) ? "extends #{@conf.sig_namer[psig]}" : ""
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
        @out.p "#{@conf.arg_namer[fld]}: "
        @out.pn [fld.type]
      end

      def fun_to_als(fun)
        args = if Class === fun.owner && fun.owner.is_sig?
                 selfarg = Arby::Ast::Arg.new :name => "self", :type => fun.owner
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
          fun_body = fun.sym_exe
          @out.pn fun_body.to_conjuncts, "\n" if fun_body
        end
        @out.pl "\n}"
      end

      def command_to_als(cmd)
        name = (cmd.name.empty?) ? "" : "#{cmd.name} "
        @out.p "#{cmd.kind} #{name}"
        if cmd.fun && cmd.fun.body
          @out.pl "{"
          @out.in do
            @out.pn [cmd.fun.sym_exe]
          end
          @out.pl
          @out.p "} "
        end
        @out.pl "#{cmd.scope}"
      end

      def type_to_als(type)
        case type
        when Arby::Ast::NoType
          @out.p "univ"
        when Arby::Ast::UnaryType
          cls = type.klass
          if cls <= Arby::Ast::ASig
            @out.p @conf.sig_namer[cls]
          else
            @out.p type.cls.to_s.relative_name
          end
        when Arby::Ast::ProductType
          @out.pn [type.lhs]
          @out.p " #{type.left_mult}-> "
          @out.p "(" if type.rhs.arity > 1
          @out.pn [type.rhs]
          @out.p ")" if type.rhs.arity > 1
        when Arby::Ast::ModType
          @out.p "#{type.mult} "
          @out.p "(" if type.arity > 1
          @out.pn [type.type]
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
          :top_class => Arby::Ast::Expr::MExpr,
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
          decl_str = decl_str.gsub /:/, " =" if expr.let?
          @out.pl "#{expr_kind} #{decl_str} {"
          @out.in do
            @out.pn expr.body.to_conjuncts, "\n"
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
        unless Arby::Ast::Expr::BoolConst === ite.else_expr
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
          when TRANSPOSE, CLOSURE, RCLOSURE, CARDINALITY; ue.op.to_s
          else "#{ue.op} "
          end
        @out.p "#{op_str}#{enclose ue.op, ue.sub}"
      end

      def binaryexpr_to_als(be)
        fmt = case be.op
              when JOIN    then "%{lhs}.%{rhs}"
              when SELECT  then "%{lhs}[%{rhs}]"
              when IPLUS   then "plus[%{lhs}, %{rhs}]"
              when IMINUS  then "minus[%{lhs}, %{rhs}]"
              else
                "%{lhs} #{be.op} %{rhs}"
              end
        @out.p(fmt % {lhs: encloseL(be.op, be.lhs), rhs: encloseR(be.op, be.rhs)})
      end

      def callexpr_to_als(ce)
        pre = (ce.has_target?) ? "#{export_to_als ce.target}." : ""
        fun = case f=ce.fun
              when Arby::Ast::Fun; f.name
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

      def enclose(op, expr, rhs=false)
        e_str = export_to_als(expr)
        (expr.op.precedence < op.precedence) || 
          (rhs && expr.op.precedence == op.precedence) ? "(#{e_str})" : e_str
      end
      def encloseL(op, expr) enclose(op, expr, false) end
      def encloseR(op, expr) enclose(op, expr, true) end
    end

  end
end
