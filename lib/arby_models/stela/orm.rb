require 'arby/arby_dsl'

module ArbyModels
module Stela

  extend Arby::Dsl

  alloy :ORM do
    
    abstract sig NeedHandle
    abstract sig Attribute extends NeedHandle
    abstract sig Class extends Attribute [
      attrSet: (set Attribute),
      id: (set Attribute),
      parent: (lone Class),
      isAbstract: Bool
    ]

  end



end
end
