require 'sdg_utils/track_nesting'

module SDGUtils
  module DSL

    #=========================================================================
    # == Class ClassBuilder
    #
    #=========================================================================
    class BaseBuilder
      extend SDGUtils::TrackNesting

      def self.top()             top_ctx end
      def self.get()             SDGUtils::DSL::BaseBuilder.find(self) end
      def self.find(builder_cls) find_ctx{|e| builder_cls === e} end
      def self.in_builder?()     curr = self.get and curr.in_builder? end
      def self.in_body?()        curr = self.get and curr.in_body? end

      def in_builder?() @in_builder end
      def in_body?()    @in_body end

      def build(*args, &body)
        BaseBuilder.push_ctx(self)
        @in_builder = true
        begin
          do_build(*args, &body)
        ensure
          @in_builder = false
          BaseBuilder.pop_ctx
        end
      end

      protected

      def initialize(options={})
        @options = {
          :created_mthd     => :__created,
          :eval_body_mthd   => :__eval_body,
          :finish_mthd      => :__finish,
          :create_const     => true
        }.merge!(options)
      end

      def do_build(*args, &body) fail "must override" end

      def eval_body(obj, default_eval_mthd=:class_eval, &body)
        return unless body
        ebm = @options[:eval_body_mthd]
        eval_body_mthd_name = obj.respond_to?(ebm) ? ebm : default_eval_mthd
        begin
          @in_body = true
          obj.send eval_body_mthd_name, &body
        ensure
          @in_body = false
        end
      end

      def opts_to_flat_array(*opts)
        opts.each do |opt|
          @options[opt] = Array[@options[opt]].flatten.compact
        end
      end

      def safe_send(obj, sym, *args)
        obj.send sym, *args if obj.respond_to? sym
      end
    end

  end
end
