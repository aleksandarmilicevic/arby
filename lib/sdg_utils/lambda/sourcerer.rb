require 'method_source'
require 'parser/current'

module SDGUtils
  module Lambda

    module Sourcerer
      extend self

      class NodeAnno
        attr_reader :fmt
        attr_accessor :src
        def initialize(fmt, src=nil) @fmt, @src = fmt, src end
      end

      # @param source_or_proc [String, Proc]
      def proc_to_src(source_or_proc)
        ast = case source_or_proc
              when String; parse_string(source_or_proc)
              when Proc; parse_proc(source_or_proc)
              else raise ArgumentError, "wrong type: #{source_or_proc.class}"
              end
        read_src(ast)
      end

      def parse_proc(proc)
        proc_src = proc.source rescue fail("source not available for proc #{proc}")
        parse_string(proc_src)
      end

      def parse_string(str)
        ast = Parser::CurrentRuby.parse(str)
        failparse = proc{|str=""| fail "#{str}\ncouldn't parse:\n #{str}"}
        root_block =
          case ast.type
          when :block
            ast
          # because of a bug in Parser, ast is not always :block
          when :send, :def
            msg = "expected :#{ast.type} with exactly 3 children"
            failparse[msg] unless ast.children.size == 3
            if ast.children[2].type == :block
              ast.children[2]
            else
              ast
            end
          else
            failparse["wrong root node, got :#{ast.type}"]
          end
        msg = "expected root block to have 3 children"
        failparse[msg] unless root_block.children.size == 3
        block_body = root_block.children[2]
        block_body
      end

      def read_src(node)
        if node && node.src && node.src.expression
          node.src.expression.to_source
        else
          ""
        end
      end

      def compute_src(node, node2anno)
        out = ""
        idx = 0
        anno = node2anno[node.__id__]
        return "" unless anno
        src = anno.src and return src
        fmt = anno.fmt
        node.children.each do |ch|
          ch_expr = ch.src.expression rescue nil
          if ch_expr
            ch_src = compute_src(ch, node2anno)
            out.concat fmt[idx]
            out.concat ch_src
            idx += 1
          end
        end
        out.concat fmt[idx]
        out
      end

      def reprint(node, &block)
        node2anno = annotate_for_printing(node)
        nodes_bottomup = traverse_nodes(node).reverse
        nodes_bottomup.each do |node, parent|
          yield(node, parent, node2anno) if node2anno[node.__id__]
        end
        compute_src(node, node2anno)
      end

      # @return [Hash(Integer, NodeAnno)]
      def annotate_for_printing(node, node2anno={})
        unless node.src.expression
          # empty block
          node2anno[node.__id__] = NodeAnno.new([""])
        else
          node_src = node.src.expression
          pos = node_src.begin_pos
          fmt = []
          ch_to_anno = []
          node.children.each do |ch|
            ch_expr = ch.src.expression rescue nil
            if ch_expr
              ch_beg = ch_expr.begin_pos
              fmt << node_src.source_buffer.source[pos...ch_beg]
              pos = ch_expr.end_pos
              ch_to_anno << ch
            end
          end
          fmt << node_src.source_buffer.source[pos...node_src.end_pos]
          node2anno[node.__id__] = NodeAnno.new(fmt)
          ch_to_anno.each{|n| annotate_for_printing(n, node2anno)}
        end
        node2anno
      end


      def traverse_nodes(node, visit_opts={}, visitor_obj=nil, &visitor_blk)
        visitor =
          case visitor_obj
          when NilClass
            v = Object.new
            if visitor_blk
              v.define_singleton_method :visit, visitor_blk
            else
              v.singleton_class.class_eval "def visit(*args) :next end"
            end
            v
          when Hash
            v = Object.new
            visitor_obj.each{|key,val| v.define_singleton_method key.to_sym, val}
            v
          else
            visitor_obj
          end

        # array of (node, parent) pairs
        visited_nodes = []
        worklist = [[node, nil]]
        while !worklist.empty? do
          node, parent = worklist.shift
          visited_nodes << [node, parent]
          what_next = visit_node(node, parent, visit_opts, visitor)
          case what_next
          when :break; break
          when :skip_children; continue
          else
            chldrn = node.children.map{|ch| [ch, node] if Parser::AST::Node===ch}.compact
            worklist.unshift(*chldrn)
          end
        end
        visited_nodes
      end

      private

      def visit_node(node, parent, opts, visitor)
        meth = case m=opts[:meth]
               when NilClass; :visit
               when :type; :"visit_#{node.type}"
               else m.to_sym
               end
        default_ret = opts[:default_ret] || :next
        if visitor.respond_to? meth
          visitor.send meth, node, parent
        else
          default_ret
        end
      end

    end

  end
end
