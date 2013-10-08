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
       
        when Ops::EQUALS, Ops::NOT_EQUALS , Ops::IN, Ops::NOT_IN, Ops::SELECT
          check_arity args, 2, "BinaryExpr requires 2 argument"
          ans = Expr::BinaryExpr.new(op, *args)
          # oans.set_type(type)
          #result_type = nil #TODO ...
          #Expr.add_methods_for_type(ans, result_type)

         ##integers
        when Ops::LT, Ops::LTE, Ops::GT, Ops::GTE, Ops::REM, Ops::NOT_LT, 
             Ops::NOT_LTE, Ops::NOT_GT, Ops::NOT_GTE, Ops::IPLUS, Ops::IMINUS,
             Ops::DIV, Ops::MUL, Ops::PLUSPLUS
          check_arity args, 2, "BinaryExpr requires 2 argument"
          ans = Expr::BinaryExpr.new(op, *args)

        #non-integers
        when Ops::PLUS, Ops::MINUS
          check_arity args, 2, "BinaryExpr requires 2 argument"
          ans = Expr::BinaryExpr.new(op, *args)

        #logic op  
        when Ops::SHL, Ops::SHA, Ops::SHR, Ops::AND, Ops::OR, Ops::IFF, Ops::IMPLIES
          check_arity args, 2, "BinaryExpr requires 2 argument"
          ans = Expr::BinaryExpr.new(op, *args)

        when Ops::JOIN, Ops::PRODUCT, Ops::DOMAIN, Ops::RANGE, Ops::INTERSECT
          check_arity args, 2, "BinaryExpr requires 2 argument"
          ans = Expr::BinaryExpr.new(op, *args)

        #Quantifier op
        when Ops::LET, Ops::SUM, Ops::SETCPH, Ops::ALLOF, Ops::SOMEOF, Ops::NONEOF,
             Ops::ONEOF, Ops::LONEOF
             ans = Expr::QuantExpr.new(op, *args)
        end
      end

      def check_arity(arr, expected_arity, err_msg=nil)
        msg = "expected arity: #{expected_arity}, actual: #{arr.length}"
        msg += err_msg if err_msg
        raise ArgumentError, msg unless arr.length == expected_arity
      end
    end



      # multiplicity type modifiers
     # SET         = Mop.new(:"set",        "set",         8)
      #SEQ         = Mop.new(:"seq",        "set",         8)


      #ITEExpr.new(cond, te, ee)
      #IF_ELSE   = Op.new(:"=>else", "if_else", 3, 4)





    module TypeComputer
      extend self

      # @param op [Alloy::Ast::Op] --- operator
      # @param args [Array(Alloy::Ast::MExpr)] --- operands
      def compute_type(op, *args)
        unless args.all?{|a| a.respond_to?(:__type) && a.__type}
          return nil
        end
        types = args.map(&:__type)
        case op
        when Ops::PRODUCT
          types[1..-1].reduce(types[0]){|acc, type| Alloy::Ast::AType.product(acc, type)}
        #TODO: finish
        end
      end
    end

  end
end
