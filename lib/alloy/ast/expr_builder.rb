require 'alloy/ast/op'
require 'alloy/ast/expr'

module Alloy
  module Ast

    #TODO: move the "__type" method to MExpr

    module ExprBuilder
      extend self

      # Keep track of result type
      #
      # @param op [Alloy::Ast::Op] --- operator
      # @param args [Array(Expr)] --- operands
      def apply(op, *args)
        case op
        when Ops::UNKNOWN
          raise ArgumentError, "Cannot apply the unknown operator"
        when Ops::PRODUCT
          # TODO: check that args.length == 2
          ans = Expr::BinaryExpr.new(op, *args)
          type = TypeComputer.compute_type(op, *ans.children)
          ans.set_type(type) if type
          ans
        ##binary operators
         ##boolean 

        #unary operators
        when Ops::NOT, Ops::NO, Ops::SOME, Ops::LONE, Ops::ONE, Ops::TRANSPOSE,
             Ops::RCLOSURE, Ops::CLOSURE, Ops::CARDINALITY, Ops::NOOP
          check_arity args, 1, "UnaryExpr requires 1 argument"
          ans = Expr::UnaryExpr.new(op, *args)
          type = TypeComputer.compute_type(op, *ans.children)
          ans.set_type(type) if type
          ans

       
        when Ops::EQUALS, Ops::NOT_EQUALS , Ops::IN, Ops::NOT_IN
          check_arity args, 2, "BinaryExpr requires 2 argument"
          ans = Expr::BinaryExpr.new(op, *args)
          type = TypeComputer.compute_type(op,*ans.children)
          ans.set_type(type) if type
          ans

         ##integers
         #compute types, and if possible try to compute types
        when Ops::LT, Ops::LTE, Ops::GT, Ops::GTE, Ops::NOT_LT, 
             Ops::NOT_LTE, Ops::NOT_GT, Ops::NOT_GTE, Ops::IPLUS, Ops::IMINUS, Ops::REM,
             Ops::DIV, Ops::MUL, Ops::PLUSPLUS
          check_arity args, 2, "BinaryExpr requires 2 argument"
          ans = Expr::BinaryExpr.new(op, *args)
          type = TypeComputer.compute_type(op,*ans.children)
          ans.set_type(type) if type
          ans

        #non-integers
        when Ops::PLUS, Ops::MINUS, Ops::SELECT
          check_arity args, 2, "BinaryExpr requires 2 argument"
          ans = Expr::BinaryExpr.new(op, *args)

        #logic op  
        when Ops::SHL, Ops::SHA, Ops::SHR, Ops::AND, Ops::OR, Ops::IFF, Ops::IMPLIES
          check_arity args, 2, "BinaryExpr requires 2 argument"
          ans = Expr::BinaryExpr.new(op, *args)
          type = TypeComputer.compute_type(op,*ans.children)
          ans.set_type(type) if type
          ans


        when Ops::JOIN, Ops::PRODUCT, Ops::DOMAIN, Ops::RANGE, Ops::INTERSECT
          check_arity args, 2, "BinaryExpr requires 2 argument"
          ans = Expr::BinaryExpr.new(op, *args)

        #Quantifier op  #ignore types
        when Ops::LET, Ops::SUM, Ops::SETCPH, Ops::ALLOF, Ops::SOMEOF, Ops::NONEOF,
             Ops::ONEOF, Ops::LONEOF
             ans = Expr::QuantExpr.new(op, *args)

        #ITE expression 
        when Ops:: IF_ELSE
          ans = Expr::ITEExpr.new(ops, *args)     
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
        unless args.all?{|a| a.respond_to?(:__type) && a.__type} # check only when we care about the type
          binding.pry
          return nil
        end
        types = args.map(&:__type)
        case op

        when Ops::UNKNOWN
          Alloy::Ast::NoType
          
        when Ops::PRODUCT
          types[1..-1].reduce(types[0]){|acc, type| Alloy::Ast::AType.product(acc, type)}
        #when Ops::JOIN
         #    Alloy::Ast::AType.join(acc, type)
        #    only on binary op , join on lhs and rhs 
        #Ops::NOT
         # bool
        #, Ops::NO, Ops::SOME, Ops::LONE, Ops::ONE, 
         # bool . are applied on a set and return a bool

        #Ops::SELECT
         # hash k -> v h[x] return value get the type of the argument 
        when Ops::EQUALS, Ops::NOT_EQUALS,Ops::IN, Ops::NOT_IN
          Alloy::Ast::AType.get(:Bool)

        when Ops::IPLUS, Ops::IMINUS, Ops::REM, Ops::DIV, Ops::MUL, Ops::PLUSPLUS
          Alloy::Ast::AType.get(:Integer)

        when Ops::LT, Ops::LTE, Ops::GT, Ops::GTE, Ops::NOT_LT, 
             Ops::NOT_LTE, Ops::NOT_GT, Ops::NOT_GTE
          Alloy::Ast::AType.get(:Bool)

        when Ops::SHL, Ops::SHA, Ops::SHR
          Alloy::Ast::AType.get(Integer)

        when Ops::AND, Ops::OR, Ops::IFF, Ops::IMPLIES
          Alloy::Ast::AType.get(:Bool)

        when Ops::CARDINALITY
          Alloy::Ast::AType.get(:Integer)

        when Ops::ALLOF, Ops::SOMEOF, Ops::NONEOF,Ops::ONEOF, Ops::LONEOF
          Alloy::Ast::AType.get(:Bool)

      #  when Ops::TRANSPOSE
       #   AType.transpose(types[0])  #how to turn this to the right type. As in how to get the type of sigA/ maybe Alloy::Ast::AType.get?

        when Ops::SUM
          Alloy::Ast::AType.get(:Integer)

        end
      end
    end

  end
end
