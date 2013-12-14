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

    sig :File < Obj {
      some d: Folder do in? d.entries.contents end
    }

    sig Folder extends Obj [
      entries: (set Entry),
      parent: (lone Folder)
    ] {
      parent == contents!.entries! and
      not_in? self.^:parent and
      (self.*:parent).contains?(Root) and
      all [:e1, :e2] => entries do
        e1 == e2 if e1.name == e2.name
      end
    }

    one sig Root extends Folder {
      no parent
    }

    lone sig Curr extends Folder

    # all directories besides root have one parent
    pred oneParent_buggyVersion {
      all d: Folder - Root do
        one d.parent
      end
    }

    # all directories besides root have one parent
    pred oneParent_correctVersion {
      all d: Folder - Root do
        one d.parent and one d.contents!
      end
    }

    # Only files may be linked (i.e., have more than one entry). That
    # is, all directories are the contents of at most one directory
    # entry.
    pred noDirAliases {
      all o: Folder do lone o.contents! end
    }

    check("for 5 expect 1") { noDirAliases if oneParent_buggyVersion }
    check("for 5 expect 0") { noDirAliases if oneParent_correctVersion }
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
  some d: Folder {
    this in d.@entries.@contents
  }
}

sig Folder extends Obj {
  entries: set Entry,
  parent: lone Folder
} {
  this.@parent = this.~@contents.~@entries
  this !in this.^@parent
  Root in this.*@parent
  all e1: this.@entries, e2: this.@entries {
    e1.@name = e2.@name => e1 = e2
  }
}

one sig Root extends Folder {} {
  no this.@parent
}

lone sig Curr extends Folder {}

pred oneParent_buggyVersion {
  all d: Folder - Root {
    one d.parent
  }
}

pred oneParent_correctVersion {
  all d: Folder - Root {
    one d.parent
    one d.~contents
  }
}

pred noDirAliases {
  all o: Folder {
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
