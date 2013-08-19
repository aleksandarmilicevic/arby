require 'method_source'
require 'parser/current'

module SDGUtils
  module Lambda

    module Sourcerer
      extend self

      def proc_to_src(proc)
        proc_src = proc.source rescue fail("source not available for proc #{proc}")
        failparse = proc{|str=""| fail "#{str}\ncouldn't parse:\n #{proc_src}"}
        ast = Parser::CurrentRuby.parse(proc.source)
        root_block =
          case
          when ast.type == :block;
            ast
          # because of a bug in Parser, ast is not always :block
          when ast.type == :send
            msg = "expected :send with exactly 3 children"
            failparse[msg] unless ast.children.size == 3
            msg = "expected :send where the 3rd children is a :block node"
            failparse[msg] unless ast.children[2].type == :block
            ast.children[2]
          else
            failparse["wrong root node: expected :block or :send, got :#{ast.type}"]
          end
        msg = "expected root block to have 3 children"
        failparse[msg] unless root_block.children.size == 3
        block_body = root_block.children[2]
        if block_body.type == :nil
          ""
        else
          block_body.src.expression.to_source
        end
      end

      alias_method :lambda_to_src, :proc_to_src
    end

  end
end
