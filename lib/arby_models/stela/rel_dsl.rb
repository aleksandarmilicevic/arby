require 'arby/arby_dsl'
require 'arby_models/stela/obj_dsl'

module ArbyModels
module Stela

  extend Arby::Dsl

  alloy :RelDSL do
    open ObjDSL

    sig Field [ 
      fAssociate: (one NeedHandle)
    ]
    sig Table [
      fields: (set Field),
      primaryKey: (set Field),
      foreignKey: (set Field),
      tAssociate: (set Klass+Association)
    ] {
      some tAssociate
    }
    
    fact {
      all(n: NeedHandle)  { lone n.~(fAssociate) }  and
      all(c: Klass)       { lone c.~(tAssociate) }  and
      all(a: Association) { lone a.~(tAssociate) }  and
      Field.in? Table.fields                        and
      no (Field.(fAssociate) & (Association+Klass)) and
      # TODO: foreignKey.(fAssociate).ran in id.ran and
      Attribute.in? (Field.(fAssociate) + Klass.(isAbstract) + Klass) and
      all(c: Klass) {
        if c.~(tAssociate) == c.~(parent).~(tAssociate) || c.~(tAssociate) == c.parent.~(tAssociate)
          c.~(tAssociate).fields.in? (c.~(tAssociate).foreignKey + 
                                      c.attrSet.~(fAssociate) +
                                      c.^(parent).attrSet.~(fAssociate))
        end
      }
     
    }
  end



end
end
