require 'arby/arby_dsl'
require 'arby_models/stela/obj_dsl'
require 'arby_models/stela/rel_dsl'
require 'arby_models/stela/customer'

module ArbyModels
module Stela

  extend Arby::Dsl

  alloy :ORM do
    # open ObjDSL
    open RelDSL
    # open CustomerModel

    pred oneAssocFieldKlass[a: Attribute, c: Klass] {
      one(f: Field) { 
        f.fAssociate == a            and 
        f.in? c.~(tAssociate).fields
      }
    }

    pred unionSubclass[c: Klass] {
      # Assinging a table to the concrete class 
      if c.in? isAbstract.(No)
        one(t: Table) { t.tAssociate == c && t.tAssociate.size == 1 }
      end                                                               and
  
      c.~(tAssociate).size == 1                                         and
      c.~(tAssociate).fields.size == c.*(parent).attrSet.size           and
      # Assigning the primary Key
      c.~(tAssociate).primaryKey == c.id.~(fAssociate)                    and
      # Assigning the foreign Key
      no c.~(tAssociate).foreignKey                                     and

      # Each table encompasses relational fields corresponding to both
      # attributes of the associated class and its inherited
      # attributes.
      if c.isAbstract == No
        all(a: Attribute) | if a.in? c.attrSet 
          oneAssocFieldKlass[a, c]
          # one(f: Field) { f.fAssociate == a && f.in?(c.~(tAssociate).fields) }
        end 
      end                                                               and

      # The associated table of each concrete class should also
      # include the fields of its abstract parent's attributes
      if c.isAbstract == No && some(c.^(parent))
        all(a: Attribute) | if a.in? c.^(parent).attrSet
          oneAssocFieldKlass[a, c]
          # one(f: Field) { f.fAssociate == a && f.in?(c.~(tAssociate).fields) }
        end
      end                                                               and

      if c.isAbstract == No
        oneAssocFieldKlass[c.id, c]
        # one(f: Field) { f.fAssociate == c.id && f.in?(c.~(tAssociate).fields) }
      end                                                               
    }

    pred joinedSubclass[c: Klass] {
      one(t: Table) { t.tAssociate == c && t.tAssociate.size == 1 }    and
      c.~(tAssociate).size == 1                                        and
      oneAssocFieldKlass[c.id, c]                                      and
      # Assigning the primary Key
      c.~(tAssociate).primaryKey == c.id.~(fAssociate)                 and
      # Assigning the foreign Key
      if some c.parent
        c.~(tAssociate).foreignKey == c.parent.id.~(fAssociate)
      else
        no c.~(tAssociate).foreignKey
      end                                                              and

      # Each table encompasses relational fields corresponding to
      # non-inherited attributes of the related class all
      # a:Class.attrSet|one f:Field|f.associate=a && f in
      # a.~attrSet.~associate.fields
      all(a: Attribute) | if a.in? c.attrSet 
        oneAssocFieldKlass[a, c]
        # one(f: Field) { f.fAssociate == a && f.in?(c.~(tAssociate).fields) 
      end                                                              and

      if some c.parent
        c.~(tAssociate).fields.size == c.attrSet.size + 1
      else
        c.~(tAssociate).fields.size == c.attrSet.size
      end                                                              
    }

    pred unionSuperclass[c: Klass] {
      # If c has a child mapped by UnionSuperClass strategy, then just
      # map this class to the table to which the child is mapped
      if c.in? isAbstract.(No) 
        one Table.<(c.~tAssociate)
      end                                                              and

      # Each table encompasses relational fields corresponding to both
      # attributes of the associated class and its inherited
      # attributes.
      if c.isAbstract == No
        all(a: Attribute) | if a.in? c.*(parent).attrSet
          one(f: Field) { f.fAssociate == a && f.in?(a.~(attrSet).~(tAssociate).fields) }
        end 
      end                                                              and

      # The associated table has a type attribute to indicate the most
      # specific class for the object represented by a tuple
      one(f: Field) { 
        f.fAssociate.in? TDType      and
        f.in? c.~(tAssociate).fields and
        c.~(tAssociate).fields == c.~(tAssociate).foreignKey + 
                                  c.~(tAssociate).tAssociate.(attrSet).~(fAssociate) + 
                                  f 
      }                                                                and

      # when a subclass is assigned to be mapped by UnionSuperclass
      # strategy, all its parents in the same hierarchy are needed to
      # be mapped using the same strategy.
      c.*(parent).~(tAssociate) == c.~(tAssociate)                     and

      # Assigning the primary Key
      c.~(tAssociate).primaryKey == c.id.~(fAssociate)                 and

      # Assigning the foreign Key
      if no(a: Association) { a.dst.in? c.*(parent) }
        no c.~(tAssociate).foreignKey
      end
    }

    pred srInheritance[cs: (set Klass)] {
      all(c: cs) | if c.in? isAbstract.(No)
	one Table.<(c.~tAssociate)
      end                                                              and

      all(c: cs) | if c.isAbstract == No
        all(a: Attribute) | if a.in?(c.attrSet)
	  one(f: Field) { f.fAssociate == a && f.in?(a.~(attrSet).~(tAssociate).fields) }
        end
      end                                                              and

      all(c: cs) | if c.isAbstract == No && some(c.^parent)
        all(a: Attribute) | if a.in? c.^(parent).attrSet
          one(f: Field) { f.fAssociate == a && f.in?(c.~(tAssociate).fields) }
	end
      end                                                              and

      # The associated table has a type attribute to indicate the most
      # specific class for the object represented by a tuple
      one(f: Field) { f.fAssociate.in?(cs) && f.in?(cs.~(tAssociate).fields) }  and

      all(c: cs) { c.~(tAssociate).primaryKey == c.id.~(fAssociate) }           and

      # Assigning the foreign Key
      all(c: cs) { no c.~(tAssociate).foreignKey }
  }

  fact {
    all(t: Table) { t.tAssociate.in?(Klass+Association) }
  }

  # recently added for enabling DSE
  pred mixedStrategy[cs: (set Klass)]{
    all(c: cs) { unionSubclass[c] or joinedSubclass[c] or unionSuperclass[c] }
  }

  end

end
end
