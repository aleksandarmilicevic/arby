require 'arby/arby_dsl'
require 'arby_models/stela/obj_dsl'

module ArbyModels
module Stela

  Arby::Dsl.alloy_module :CustomerModel do
    open ObjDSL

    one sig CustomerID extends TInt
    one sig CustomerName extends TStr
    one sig OrderID extends TInt
    one sig OrderValue extends TReal
    one sig TestID extends TInt
    one sig TestName extends TStr

    one sig Customer extends Klass {
      attrSet == CustomerID + CustomerName and
      id == CustomerID                     and
      isAbstract == No                     and
      no parent
    }

    one sig Order extends Klass {
      attrSet == OrderID + OrderValue and
      id == OrderID                   and
      isAbstract == No                and
      no parent
    }

    one sig CustomerOrderAssociation extends Association {
      src == Customer  and
      dst == Order     and
      src_mult == ONE  and
      dst_mult == MANY 
    }

    one sig Test extends Klass {
      attrSet == TestID + TestName and
      id == TestID                 and
      isAbstract == No             and
      no parent
    }

    one sig TestOrderAssociation extends Association {
      src == Test      and 
      dst == Order     and
      src_mult == ONE  and
      dst_mult == MANY    
    }
  end



end
end
