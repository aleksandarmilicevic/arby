module Alloy
  module Ast

    class Op
      # both :sym and :name must be unique accross all operators
      attr_reader :sym, :name

      @@op_by_sym  = {}
      @@op_by_name = {}
      @@ops        = []

      def initialize(sym, name, arity=-1)
        @sym, @name, @arity = sym, name, arity
        @@op_by_sym.merge!({sym => self})
        @@op_by_name.merge!({name => self})
      end

      def to_s() sym.to_s end

      def self.by_sym(sym)   @@op_by_sym[sym] end
      def self.by_name(name) @@op_by_name[name] end
      def self.all()         @@ops.clone end
    end

    class Uop < Op
      def initialize(sym, name)
        super(sym, name, 1)
      end
    end

    class Bop < Op
      def initialize(sym, name)
        super(sym, name, 2)
      end
    end

    module UnaryOps
      SOMEOF      = Uop.new(:"some of",    "someof")
      LONEOF      = Uop.new(:"lone of",    "loneof")
      ONEOF       = Uop.new(:"one of",     "oneof")
      SETOF       = Uop.new(:"set of",     "setof")
      EXACTLYOF   = Uop.new(:"exactly of", "exactlyof")
      NOT         = Uop.new(:"!",          "not")
      NO          = Uop.new(:"no",         "no")
      SOME        = Uop.new(:"some",       "some")
      LONE        = Uop.new(:"lone",       "lone")
      ONE         = Uop.new(:"one",        "one")
      TRANSPOSE   = Uop.new(:"~",          "transpose")
      RCLOSURE    = Uop.new(:"*",          "rclosure")
      CLOSURE     = Uop.new(:"^",          "closure")
      CARDINALITY = Uop.new(:"#",          "cardinality")
      CAST2INT    = Uop.new(:"Int->int",   "cast2int")
      CAST2SIGINT = Uop.new(:"int->Int",   "cast2sigint")
      NOOP        = Uop.new(:"NOOP",       "noop")

      def self.all()        constants.map{|sym| const_get(sym)} end
      def self.each(&block) all.each(&block) end
    end

    module BinaryOps
      JOIN       = Bop.new(:".",   "join")
      DOMAIN     = Bop.new(:"<:",  "domain")
      RANGE      = Bop.new(:":>",  "range")
      INTERSECT  = Bop.new(:"&",   "intersect")
      PLUSPLUS   = Bop.new(:"++",  "plusplus")
      PLUS       = Bop.new(:"+",   "plus")
      IPLUS      = Bop.new(:"@+",  "iplus")
      MINUS      = Bop.new(:"-",   "minus")
      IMINUS     = Bop.new(:"@-",  "iminus")
      MUL        = Bop.new(:"*",   "mul")
      DIV        = Bop.new(:"/",   "div")
      REM        = Bop.new(:"%",   "rem")
      EQUALS     = Bop.new(:"=",   "equals")
      NOT_EQUALS = Bop.new(:"!=",  "not_equals")
      IMPLIES    = Bop.new(:"=>",  "implies")
      LT         = Bop.new(:"<",   "lt")
      LTE        = Bop.new(:"<=",  "lte")
      GT         = Bop.new(:">",   "gt")
      GTE        = Bop.new(:">=",  "gte")
      NOT_LT     = Bop.new(:"!<",  "not_lt")
      NOT_LTE    = Bop.new(:"!<=", "not_lte")
      NOT_GT     = Bop.new(:"!>",  "not_gt")
      NOT_GTE    = Bop.new(:"!>=", "not_gte")
      SHL        = Bop.new(:"<<",  "shl")
      SHA        = Bop.new(:">>",  "sha")
      SHR        = Bop.new(:">>>", "shr")
      IN         = Bop.new(:"in",  "in")
      NOT_IN     = Bop.new(:"!in", "not_in")
      AND        = Bop.new(:"&&",  "and")
      OR         = Bop.new(:"||",  "or")
      IFF        = Bop.new(:"<=>", "iff")

      def self.all()        constants.map{|sym| const_get(sym)} end
      def self.each(&block) all.each(&block) end
    end

  end
end
