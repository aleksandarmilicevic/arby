require 'arby/arby_dsl'

module ArbyModels
  extend Arby::Dsl

  alloy_model :FileSystem do
    abstract sig Obj
    sig Name

    sig Entry [
      name: Name,
      contents: Obj
    ] {
      one entries!
    }

    sig File < Obj {
      some d: Dir do in? d.entries.contents end
    }

    sig Dir extends Obj [
      entries: (set Entry),
      parent: (lone Dir)
    ] {
      parent == contents!.entries! and
      not_in? self.^(Dir::parent) and
      (self.*(Dir::parent)).contains?(Root) and
      all(e1, e2: entries) {
        e1 == e2 if e1.name == e2.name
      }
    }

    one sig Root extends Dir {
      no parent
    }

    lone sig Curr extends Dir

    # all directories besides root have one parent
    pred oneParent_buggyVersion {
      all d: Dir - Root do
        one d.parent
      end
    }

    # all directories besides root have one parent
    pred oneParent_correctVersion {
      all d: Dir - Root do
        one d.parent and one d.contents!
      end
    }

    # Only files may be linked (i.e., have more than one entry). That
    # is, all directories are the contents of at most one directory
    # entry.
    pred noDirAliases {
      all o: Dir do lone o.contents! end
    }

    check(5) { noDirAliases if oneParent_buggyVersion }
    check(5) { noDirAliases if oneParent_correctVersion }
  end

module FileSystem
  Expected_alloy = """
module FileSystem

abstract sig Obj  {}

sig Name  {}

sig Entry  {
  name: Name,
  contents: Obj
} {
  one this.~@entries
}

sig File extends Obj {} {
  some d: Dir {
    this in d.@entries.@contents
  }
}

sig Dir extends Obj {
  entries: set Entry,
  parent: lone Dir
} {
  this.@parent = this.~@contents.~@entries
  this !in this.^@parent
  Root in this.*@parent
  all e1: this.@entries, e2: this.@entries {
    e1.@name = e2.@name => e1 = e2
  }
}

one sig Root extends Dir {} {
  no this.@parent
}

lone sig Curr extends Dir {}

pred oneParent_buggyVersion {
  all d: Dir - Root {
    one d.parent
  }
}

pred oneParent_correctVersion {
  all d: Dir - Root {
    one d.parent
    one d.~contents
  }
}

pred noDirAliases {
  all o: Dir {
    lone o.~contents
  }
}

check {
  oneParent_buggyVersion[] => noDirAliases[]
} for 5 expect 1

check {
  oneParent_correctVersion[] => noDirAliases[]
} for 5 expect 0
"""
end

end
