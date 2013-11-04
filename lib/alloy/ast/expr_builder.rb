require 'alloy/ast/op'
require 'alloy/ast/expr'

module Alloy
  module Ast

    #TODO: move the "__type" method to MExpr

    module ExprBuilder
      extend self

      # Reduces the given operands (+args+) by applying the given
      # binary operator (+op+)
      #
      # @param op   [Alloy::Ast::Op] --- binary operator
      # @param args [Array(Expr)]    --- operands
      def reduce_to_binary(op, *args)
        args[1..-1].reduce(args[0]){|acc, rhs| apply(op, acc, rhs)}
      end

      # Keep track of result type
      #
      # @param op [Alloy::Ast::Op] --- operator
      # @param args [Array(Expr)] --- operands
      def apply(op, *args)
        case op
        when Ops::UNKNOWN
          raise ArgumentError, "Cannot apply the unknown operator"

        # unary operators
        when Ops::NOT, Ops::NO, Ops::SOME, Ops::LONE, Ops::ONE, Ops::TRANSPOSE,
             Ops::RCLOSURE, Ops::CLOSURE, Ops::CARDINALITY, Ops::NOOP
          check_arity args, 1, "UnaryExpr requires 1 argument"
          ans = Expr::UnaryExpr.new(op, *args)
          type = TypeComputer.compute_type(op, *ans.children)
          ans.set_type(type) if type
          ans

        # integer ops
        when Ops::SHL, Ops::SHA, Ops::SHR,
             Ops::LT, Ops::LTE, Ops::GT, Ops::GTE, Ops::NOT_LT,
             Ops::NOT_LTE, Ops::NOT_GT, Ops::NOT_GTE, Ops::IPLUS, Ops::IMINUS, Ops::REM,
             Ops::DIV, Ops::MUL, Ops::PLUSPLUS
          check_arity args, 2, "BinaryExpr requires 2 argument"
          ans = Expr::BinaryExpr.new(op, *args)
          type = TypeComputer.compute_type(op,*ans.children)
          ans.set_type(type) if type
          ans

        # logic binary ops
        when Ops::EQUALS, Ops::NOT_EQUALS , Ops::IN, Ops::NOT_IN,
             Ops::AND, Ops::OR, Ops::IFF, Ops::IMPLIES
          check_arity args, 2, "#{op} is a binary operators; #{args.size} operands given"
          ans = Expr::BinaryExpr.new(op, *args)
          type = TypeComputer.compute_type(op,*ans.children)
          ans.set_type(type) if type
          ans

        # relational binary ops
        when Ops::PLUS, Ops::MINUS, Ops::SELECT, Ops::JOIN, Ops::PRODUCT,
             Ops::DOMAIN, Ops::RANGE, Ops::INTERSECT
          check_arity args, 2, "#{op} is a binary operators; #{args.size} operands given"
          ans = Expr::BinaryExpr.new(op, *args)
          type = TypeComputer.compute_type(op, *ans.children)
          ans.set_type(type) if type
          ans

        # Quantifier op
        when Ops::LET, Ops::SUM, Ops::SETCPH, Ops::ALLOF, Ops::SOMEOF, Ops::NONEOF,
             Ops::ONEOF, Ops::LONEOF
          ans = Expr::QuantExpr.new(op, *args)
          type = TypeComputer.compute_type(op) #TODO: what args to pass to TypeComputer???
          ans.set_type(type) if type
          ans

        # ITE expression
        when Ops::IF_ELSE
          ans = Expr::ITEExpr.new(ops, *args)

        when Ops::ASSIGN
          check_arity args, 2, "#{op} is a binary operators; #{args.size} operands given"
          ans = Expr::BinaryExpr.new(op, *args)
          type = TypeComputer.compute_type(op, *ans.children)
          ans.set_type(type) if type
          ans

        else
          raise ArgumentError, "unsupported operator #{op}"
        end
      end

      def check_arity(arr, expected_arity, err_msg=nil)
        msg = "expected arity: #{expected_arity}, actual: #{arr.length}"
        msg += err_msg if err_msg
        raise ArgumentError, msg unless arr.length == expected_arity
      end
    end

    module TypeComputer
      extend self

      # @param op [Alloy::Ast::Op] --- operator
      # @param args [Array(Alloy::Ast::MExpr)] --- operands
      def compute_type(op, *args)
        # TODO: check only when we care about the operand types
        unless args.all?{|a| a.respond_to?(:__type) && a.__type}
          return nil
        end

        types = args.map(&:__type)

        case op
        when Ops::UNKNOWN
          Alloy::Ast::NoType

        when Ops::PRODUCT
          types[1..-1].reduce(types[0]){|acc, type| Alloy::Ast::AType.product(acc, type)}

        when Ops::JOIN
          Alloy::Ast::AType.join(types[0], types[1])

        when Ops::SELECT
          Alloy::Ast::AType.join(types[1], types[0])

        when Ops::PLUS
          Alloy::Ast::AType.union(*types)

        when Ops::MINUS
          Alloy::Ast::AType.difference(*types)

        when Ops::INTERSECT
          Alloy::Ast::AType.intersect(*types)

        when Ops::TRANSPOSE
          AType.transpose(types[0])

        when Ops::ASSIGN
          types.last

        when Ops::CLOSURE, Ops::RCLOSURE
          # TODO type check: types.first is a binary relation
          types.first

        when Ops::NO, Ops::SOME, Ops::LONE, Ops::ONE,
          # TODO type check: all operand types are relations
          Alloy::Ast::AType.get(:Bool)

        when Ops::EQUALS, Ops::NOT_EQUALS,Ops::IN, Ops::NOT_IN
          Alloy::Ast::AType.get(:Bool)

        when Ops::IPLUS, Ops::IMINUS, Ops::REM, Ops::DIV, Ops::MUL, Ops::PLUSPLUS,
             Ops::SHL, Ops::SHA, Ops::SHR
          #TODO type check: all operand types are integer
          Alloy::Ast::AType.get(:Integer)

        when Ops::LT, Ops::LTE, Ops::GT, Ops::GTE, Ops::NOT_LT,
             Ops::NOT_LTE, Ops::NOT_GT, Ops::NOT_GTE
          #TODO type check: all operand types are integer
          Alloy::Ast::AType.get(:Bool)

        when Ops::AND, Ops::OR, Ops::IFF, Ops::IMPLIES, Ops::NOT
          #TODO type check: all operand types are boolean
          Alloy::Ast::AType.get(:Bool)

        when Ops::CARDINALITY
          # type check: all operand types are relations
          Alloy::Ast::AType.get(:Integer)

        when Ops::ALLOF, Ops::SOMEOF, Ops::NONEOF,Ops::ONEOF, Ops::LONEOF
          Alloy::Ast::AType.get(:Bool)

        when Ops::SUM
          Alloy::Ast::AType.get(:Integer)

        end
      end
    end

  end
end
