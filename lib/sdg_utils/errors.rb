module SDGUtils
  module Errors

    class ErrorWithCause < StandardError
      def init(msg, backtrace)
        @msg = msg || ""
        @backtrace = backtrace || []
      end

      def init1(cause_or_msg)
        case cause_or_msg
        when Exception
          init2(cause_or_msg, "")
        when String
          init2(nil, cause_or_msg)
        else
          init2(nil, "")
        end
      end

      def initialize(cause=nil)
        @cause = cause
        @tab = "  "
      end

      def self.inherited(subclass)
        subclass.instance_eval do
          def initialize(cause=nil);   super end
        end
      end

      def exception(*args)
        case args.size
          when 1
            init(args[0], caller)
          when 2
            init(*args)
        end
        self
      end

      def to_s
        full_message
      end

      def full_message
        format_msg ""
      end

      def format_msg(indent)
        new_indent = @msg.empty? ? indent : indent + @tab
        cause_msg = case @cause
                    when NilClass
                      ""
                    when ErrorWithCause
                      @cause.format_msg(new_indent)
                    when Exception
                      new_indent + "#{@cause.message} (#{@cause.class})"
                    else
                      new_indent + @cause.to_s
                    end
        "#{indent}#{@msg} (#{self.class})\n#{cause_msg}"
      end

      def backtrace
        full_backtrace
      end

      def full_backtrace
        ret = ["#{self.class}"]
        ret += @backtrace || []
        if @cause != nil
          ret += ["", "Caused by #{@cause.class}: #{@cause.message}"]
          ret += @cause.backtrace.map{|e| @tab + e}
        end
        ret
      end

    end

  end
end
