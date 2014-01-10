require 'arby/arby_dsl'

Arby.conf.sym_exe.convert_missing_fields_to_joins = true

module ArbyModels
  extend Arby::Dsl

  alloy :Grandpa do
    abstract sig Person [
      father: (lone Man),
      mother: (lone Woman)
    ] {
      not in? this.^(Person.father + Person.mother)
    }

    sig Man extends Person [
      wife: (lone Woman)
    ]

    sig Woman extends Person [
      husband: (lone Man)
    ]

    fact terminology { wife == ~husband }
    fact biology     { no(p: Person){ p.in? p.^(father+mother) } }

    fact socialConvention {
      no wife & (mother+father).rclosure.mother and
      no husband & (mother+father).rclosure.father
    }

    fun grandpas[p: Person][set Person] {
      let(parent: mother + father + father.wife + mother.husband) {
        p.parent.parent & Man
      }
    }

    pred ownGrandpa[m: Man] {
      m.in? grandpas(m)
    }

    run :ownGrandpa, "for 4 Person"

    # fact socialConvention2 {
    #   no wife & mother.*(~(mother+father)) and
    #   no husband & father.*(~(mother+father))
    # }

    # fun grandpas2[p: Person][set Person] {
    #   parent = mother + father + father.wife + mother.husband
    #   p.join(parent).join(parent) & Man
    # }
  end
end
