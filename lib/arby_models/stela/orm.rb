require 'arby/arby_dsl'
require 'arby_models/stela/obj_dsl'
require 'arby_models/stela/rel_dsl'

module ArbyModels
module Stela

  extend Arby::Dsl

  alloy :ORM do
    # open ObjDSL
    open RelDSL
  end



end
end
