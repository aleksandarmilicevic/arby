require 'arby/arby_dsl'
require 'arby_models/stela/obj_dsl'

module ArbyModels
module Stela

  Arby::Dsl.alloy :RelDSL do
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

    pred oneAssocField[a: Attribute] {
      one(f: Field) {
        f.fAssociate == a   and
        one f.fAssociate    and 
        one a.~(fAssociate) and
        f.in? a.~(attrSet).~(tAssociate).fields
      }
    }

    pred assocEnd[aEnd: Klass] {
      all(a: aEnd.attrSet) { oneAssocField[a] if a.not_in? Klass }         and
      aEnd.~(tAssociate).fields.in? (aEnd.~(tAssociate).foreignKey +
                                     aEnd.~(tAssociate).tAssociate.(attrSet).~(fAssociate) +
                                     TDType.~(fAssociate))                 
    }

    pred fKeysForMany[asc: Association] {
      (asc.dst.~(tAssociate)).foreignKey.size == Association.select{ |a| 
        a.dst == asc.dst && a.dst_mult == MANY && no(a.~(tAssociate))
      }.size                                                                  and
      (asc.src.~(tAssociate)).foreignKey.size == Association.select{ |a| 
        a.dst == asc.src && a.dst_mult == MANY && no(a.~(tAssociate))
      }.size
    }

    pred foreignKeyEmbedding[asc: Association] {
      one(t: Table) { t.tAssociate == asc.dst }                               and
      no(t: Table)  { t.tAssociate == asc }                                   and
      if !((asc.src.~(tAssociate) == asc.src.~(parent).~(tAssociate)) || 
           (asc.src.~(tAssociate) == asc.src.parent.~(tAssociate)))
        one(t: Table) { t.tAssociate == asc.src }
      end                                                                     and
      no asc.~(tAssociate)                                                    and
      one asc.dst.~(tAssociate)                                               and
      one asc.src.~(tAssociate)                                               and
      assocEnd[asc.src] and
      assocEnd[asc.dst] and

      asc.src.~(tAssociate).primaryKey == asc.src.id.~(fAssociate)            and
      asc.dst.~(tAssociate).primaryKey == asc.dst.id.~(fAssociate)            and

      asc.src.~(tAssociate).primaryKey.in? asc.dst.~(tAssociate).fields       and
      asc.src.~(tAssociate).primaryKey.in? (asc.dst.~(tAssociate)).foreignKey and

      fKeysForMany[asc]
    }

    pred ownAssociationTable[asc: Association] {
      one(t: Table) { asc.src.in? t.tAssociate }                      and
      one(t: Table) { asc.dst.in? t.tAssociate }                      and
      one(t: Table) { t.tAssociate == asc }                           and
      one asc.~tAssociate                                             and
      one asc.src.~tAssociate                                         and
      one asc.dst.~tAssociate                                         and
      assocEnd[asc.src] and
      assocEnd[asc.dst] and
 
      asc.src.~(tAssociate).primaryKey == asc.src.id.~(fAssociate)    and
      asc.dst.~(tAssociate).primaryKey == asc.dst.id.~(fAssociate)    and

      asc.~(tAssociate).primaryKey == asc.src.~(tAssociate).primaryKey + 
                                      asc.dst.~(tAssociate).primaryKey     and
      asc.~(tAssociate).foreignKey == asc.src.id.~(fAssociate) + 
                                      asc.dst.id.~(fAssociate)             and

      asc.~(tAssociate).fields == asc.src.~(tAssociate).primaryKey + 
                                  asc.dst.~(tAssociate).primaryKey         and

      asc.~(tAssociate).fields.size == 2                                   and
      fKeysForMany[asc]
    }

    pred mergingOneTable[asc: Association] {
	one(t: Table) {
          t.tAssociate == asc + asc.src + asc.dst and
          t.tAssociate.size == 3
        }                                                 and
	asc.~(tAssociate) == 1                            and

        # Each basic attribute is assigned to a field of the related table
        all(a: asc.(src+dst).attrSet) {
          if a.not_in? Klass 
            one(f: Field) { f.fAssociate == a && f.in?(a.~(attrSet).~(tAssociate).fields) }
          end
        }                                                                            and

        one(f: Field) { f.fAssociate == asc.src && f.in?(asc.~(tAssociate).fields) } and
        one(f: Field) { f.fAssociate == asc.dst && f.in?(asc.~(tAssociate).fields) } and

        # Each Field handles only one association
        Field.size == Field.(fAssociate).size                                        and

        # In one-to-one association relationships, the primary key of
        # the table associated to the combination of Classes and their
        # Association can be the primary key of either of classes,
        # here it is assigned to the primary key of the src of the
        # association
        asc.~(tAssociate).primaryKey == Field.<(asc.src.id.~fAssociate)
    }

    pred mixedAssociationMapping[asc: Association] {
      if asc.src_mult == ONE
        ownAssociationTable[asc] or foreignKeyEmbedding[asc] 
      else
 	ownAssociationTable[asc]
     	# ForeignKeyEmbedding[asc]
      end
    }

    pred mixedAssociationStrategy[asc: (set Association)] {
      all(c: asc) | mixedAssociationMapping[c]
    }

    # Each Class or Association is handled by just one Table At most one
    # Table is assigned to each Class or Association In "Meging into
    # single" and "Own association Table" strategies it would be exactly
    # one Table for each Class or Association In "Foreign Key embedding"
    # strategy it would be exactly one Table per Class, and no Table per
    # Association
    fact oneTablePerClassAndAssociation {
      # At most one Table is assigned to each Class involved in an association
      all(asc: Association) {
        Table.<(asc.src.~tAssociate).size == 1 and
        Table.<(asc.dst.~tAssociate).size == 1
      }
    }
  end

end
end
