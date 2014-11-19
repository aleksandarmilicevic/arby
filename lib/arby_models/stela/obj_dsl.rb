require 'arby/arby_dsl'

module ArbyModels
module Stela

  extend Arby::Dsl

  alloy :ObjDSL do
    
    abstract sig NeedHandle
    abstract sig Attribute extends NeedHandle
    abstract sig Klass extends Attribute [
      attrSet: (set Attribute),
      id: (set Attribute),
      parent: (lone Klass),
      isAbstract: TBool
    ]
    abstract sig Type extends Attribute
    sig TInt extends Type
    sig TStr extends Type
    sig TBool extends Type
    sig Yes extends TBool
    sig No extends TBool
    sig TDType extends Type
    sig TLongblob extends Type
    sig TTime extends Type

    abstract sig Mult_State
    one sig ONE extends Mult_State
    one sig MANY extends Mult_State

    abstract sig Association extends NeedHandle [
      src: (one Klass),
      dst: (one Klass),
      src_mult: (one Mult_State),
      dst_mult: (one Mult_State)
    ]
  end



end
end
