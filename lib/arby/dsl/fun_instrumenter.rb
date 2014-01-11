require 'sdg_utils/lambda/sourcerer'

module Arby
  module Dsl

    class FunInstrumenter
      include SDGUtils::Lambda::Sourcerer

      def initialize(proc)
        @proc = proc
      end

      def instrument
        ast = parse_proc(@proc)
        return ["", ""] unless ast
        orig_src = read_src(ast)
        instr_src = reprint(ast) do |node, parent, anno|
          case node.type
          when :if then
            cond_src = compute_src(node.children[0], anno)
            then_src = compute_src(node.children[1], anno)
            else_src = compute_src(node.children[2], anno)
            if else_src.empty?
              "Arby::Ast::Expr::BinaryExpr.implies(" +
                "proc{#{cond_src}}, proc{#{then_src}}) "
            else
              "Arby::Ast::Expr::ITEExpr.new(" +
                "proc{#{cond_src}}, " +
                "proc{#{then_src}}, " +
                "proc{#{else_src}})"
            end
          when :and, :or then
            lhs_src = compute_src(node.children[0], anno)
            rhs_src = compute_src(node.children[1], anno)
            "Arby::Ast::Expr::BinaryExpr.#{node.type}(" +
              "proc{#{lhs_src}}, " +
              "proc{#{rhs_src}})"
          else
            nil
          end
        end
        [orig_src, instr_src]
      end
    end

  end
end
