require 'arby/arby_dsl'
require 'arby_models/stela/obj_dsl'
require 'arby_models/stela/rel_dsl'
require 'arby_models/stela/customer'

module ArbyModels
module Stela

  extend Arby::Dsl

  alloy :ORM do
    # open ObjDSL
    # open CustomerModel
    open RelDSL
  end



end
end
