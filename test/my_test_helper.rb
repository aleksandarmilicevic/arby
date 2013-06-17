ENV["RAILS_ENV"] = "test"

$LOAD_PATH << File.expand_path('../../lib', __FILE__)
$LOAD_PATH << File.expand_path('../..', __FILE__)

require 'set'
require 'test/unit'

require 'alloy/alloy'
require_relative 'unit_test_ext.rb'

Alloy.set_default :logger => Logger.new(STDOUT) 

