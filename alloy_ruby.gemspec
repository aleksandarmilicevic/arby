require 'rubygems'

Gem::Specification.new do |s|
  s.name = "alloy_ruby"
  s.author = "Aleksandar Milicevic"
  s.email = "aleks@csail.mit.edu"
  s.version = "0.0.1"
  s.summary = "Alloy DSL embedded in Ruby"
  s.description = "Embedding of the Alloy modeling language into Ruby"
  s.files = Dir['lib/**/*.rb']
  s.require_paths = ["lib"]
end
