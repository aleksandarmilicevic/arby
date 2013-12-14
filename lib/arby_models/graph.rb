require 'arby/arby_dsl'

module ArbyModels
  extend Arby::Dsl

  alloy_model :Graph do

    sig Node [
      label: Int
    ]

    sig Edge [
      src: Node,
      dst: Node,
      cost: Int
    ]

    sig Graph [
      nodes: (set Node),
      edges: (set Edge)
    ]

  end
end
