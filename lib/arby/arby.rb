require 'arby/arby_conf'
require 'arby/arby_event_constants'

require 'sdg_utils/test_and_set'
require 'sdg_utils/meta_utils'
require 'sdg_utils/timing/timer'

$perf_timer = SDGUtils::Timing::Timer.new

module Arby
  extend self

  include EventConstants

  class CMain
    include TestAndSet

    SYMBOLIC_MODE = :symbolic
    CONCRETE_MODE = :concrete

    def initialize
      reset_fields
    end

    def reset_fields
      @fields_resolved = false
      @inv_fields_added = false
      @conf = nil
      @arby_files = Set.new + Dir[File.join(File.dirname(__FILE__), "{**/*.rb}")]
    end

    public

    def exe_mode()             @exe_mode ||= CONCRETE_MODE end
    def symbolic_mode?()       exe_mode == SYMBOLIC_MODE end
    def concrete_mode?()       exe_mode == CONCRETE_MODE end
    def restore_exe_mode(mode) @exe_mode = mode end
    def set_symbolic_mode()    @exe_mode = SYMBOLIC_MODE end
    def set_concrete_mode()    @exe_mode = CONCRETE_MODE end

    def in_mode(mode)
      curr_mode = @exe_mode
      @exe_mode = mode
      yield
    ensure
      restore_exe_mode(curr_mode)
    end
    def in_symbolic_mode() in_mode(SYMBOLIC_MODE){ yield } end
    def in_concrete_mode() in_mode(CONCRETE_MODE){ yield } end

    def is_arby_file?(filename)
      @arby_files.member?(filename)
    end

    def is_caller_from_arby?(caller_str)
      m = caller_str.match(/([^:]*):/) and is_arby_file?(m.captures[0])
    end

    def meta
      require 'arby/arby_meta'
      @meta ||= Arby::Model::MetaModel.new
    end

    def boss
      require 'arby/arby_boss'
      @boss ||= Arby::BigBoss.new
    end

    def conf
      require 'arby/arby_conf'
      @conf ||= def_conf.dup
    end

    def initializer
      require 'arby/initializer'
      @initializer ||= Arby::CInitializer.new
    end

    def set_default(hash)
      def_conf.merge!(hash)
      conf.merge!(hash)
    end

    def reset
      #meta.reset
      reset_fields
    end

    def fields_resolved?; @fields_resolved end
    def inv_fields_added?; @inv_fields_added end

    private

    def def_conf
      @def_conf ||= Arby::default_conf
    end
  end

  def alloy; @@alloy ||= Arby::CMain.new end
  alias_method :main, :alloy


  extend SDGUtils::Delegate
  delegate :meta, :boss, :conf, :set_default, :initializer, :reset,
           :fields_resolved?, :inv_fields_added?, :test_and_set,
           :is_arby_file?, :is_caller_from_arby?,
           :exe_mode, :symbolic_mode?, :concrete_mode?,
           :restore_exe_mode, :set_symbolic_mode, :set_concrete_mode,
           :in_mode, :in_symbolic_mode, :in_concrete_mode,
           :to => proc{alloy}, :proc => true


  def self.instrument_methods_for_timing(*method_specs)
    method_specs.each do |full_method_spec|
      arr = full_method_spec.split("#")
      if arr.size == 2
        cls_name, meth_spec = arr
        is_static = false
      else
        arr = full_method_spec.split(".")
        if arr.size == 2
          cls_name, meth_spec = arr
          is_static = true
        end
      end
      raise "invalid method spec: #{full_method_spec}" if arr.size != 2
      cls = SDGUtils::MetaUtils.str_to_class(cls_name) and
        begin
          cls = cls.singleton_class if is_static
          meth = cls.instance_method(meth_spec)
          new_name = "#{meth.name}_#{SDGUtils::Random.salted_timestamp()}"
          cls.send :alias_method, new_name, meth.name
          cls.send :remove_method, meth.name
          cls.send :class_eval, "def #{meth.name}(*args, &blk) $perf_timer.time_it('#{full_method_spec}', self) {#{new_name}(*args, &blk)} end"
        end
    end
  end

end


# pre-require all arby files
#
# NOTE: potentially (theoretically) extremely slow (factorial complexity),
#       but seems fine in practice for the current set of Arby files
parent_dir = File.expand_path("..", __FILE__)
left_to_require = Dir[parent_dir + "/**/*.rb"] - [__FILE__]
while left_to_require.size > 0 do
  failed_to_require = []
  left_to_require.each do |f|
    begin
      require f
    rescue => e
      failed_to_require << f
    end
  end
  left_to_require = failed_to_require
end
