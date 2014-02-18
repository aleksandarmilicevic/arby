module Arby
  module Ast

    class Command
      def self.new_check(name, scope, body) self.new(:check, name, scope, body) end
      def self.new_run(name, scope, body)   self.new(:run, name, scope, body) end

      attr_reader :kind, :name, :scope, :body

      def initialize(kind, name, scope, body)
        @kind = kind
        @name = name || ""
        @scope = scope
        @body = body
      end

      def run?()   @kind == :run end
      def check?() @kind == :check end

      def to_s()    "#{kind} #{name}#{body ? ' {...}' : ''} #{scope}" end
      def inspect() to_s end

      def has_body?
        case @body
        when NilClass then false
        when Fun      then !!@body.body
        else               !!@body
        end
      end

      def body_expr(*a)
        case @body
        when NilClass    then nil
        when Fun         then @body.sym_exe(*a)
        when Expr::MExpr then @body.exe
        else             fail "unknown body: #{@body}:#{@body.class}"
        end
      end
    end

  end
end
