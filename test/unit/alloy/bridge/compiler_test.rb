require '/Users/potter/MIT/4thyear/Fall2013/6uap/arby/lib/alloy/bridge/compiler'
model = "sig A { f: set A}\n\n run { #f > 1 } for 4"
binding.pry