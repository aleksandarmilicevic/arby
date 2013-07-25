ENV["RAILS_ENV"] = "test"

$LOAD_PATH << File.expand_path('../../lib', __FILE__)
$LOAD_PATH << File.expand_path('../..', __FILE__)

require 'set'
require 'test/unit'

require 'alloy/alloy'
require 'red/red_conf'
require_relative 'unit_test_ext.rb'

Alloy.set_default :logger => Logger.new(NilIO.instance) # Logger.new(STDOUT)

# red config
c = Red::default_conf
c.view_deps.log = Logger.new(NilIO.instance)

Red.define_singleton_method :default_conf, lambda {c}

