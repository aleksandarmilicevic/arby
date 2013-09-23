require 'my_test_helper'
require 'alloy/helpers/test/dsl_helpers'
require 'alloy/initializer.rb'

include Alloy::Dsl

alloy_model :A_M_FST do
  abstract sig Obj
  sig Name

  sig Entry [
    name: Name,
    contents: Obj
  ] {
    one self.entries!
  }

  sig :File < Obj {
    some d: Folder do self.in? d.entries.contents end
  }

  sig Folder extends Obj [
    entries: (set Entry),
    parent: (lone Folder)
  ] {
    parent == self.contents!.entries! and
    self.not_in? self.^:parent and
    (self.*:parent).contains?(Root) and
    all e1: Entry, e2: Entry do     # make it so that decl can be any expr
      e1 == e2 if (e1 + e2).in?(entries) && e1.name == e2.name
    end
  }

  one sig Root extends Folder {
    no parent
  }

  lone sig Curr extends Folder

  # all directories besides root have one parent
  pred oneParent_buggyVersion {
    all d: Folder do
      if d.not_in?(Root)
        one d.parent
      end
    end
  }

  # all directories besides root have one parent
  pred oneParent_correctVersion {
    all d: Folder do
      if d.not_in?(Root)
        one d.parent and
        one d.contents!
      end
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

Expected_alloy = """
module A_M_FST

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
  all e1: Entry, e2: Entry {
    e1 + e2 in this.@entries && e1.@name = e2.@name => e1 = e2
  }
}

one sig Root extends Folder {} {
  no this.@parent
}

lone sig Curr extends Folder {}

pred oneParent_buggyVersion {
  all d: Folder {
    d !in Root => one d.parent
  }
}

pred oneParent_correctVersion {
  all d: Folder {
    d !in Root => one d.parent && one d.~contents
  }
}

pred noDirAliases {
  all o: Folder {
    lone o.~contents
  }
}

check  {
  oneParent_buggyVersion[] => noDirAliases[]
} for 5 expect 1

check  {
  oneParent_correctVersion[] => noDirAliases[]
} for 5 expect 0
"""

class FileSystemTest < Test::Unit::TestCase
  include Alloy::Helpers::Test::DslHelpers
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions

  include A_M_FST

  def setup_class
    Alloy.reset
    Alloy.meta.restrict_to(A_M_FST)
    Alloy.initializer.resolve_fields
    Alloy.initializer.init_inv_fields
  end

  def test
    ans = Alloy.meta.to_als
    puts ans
    assert_equal Expected_alloy.strip, ans.strip
  end
end
