require 'my_test_helper'
require 'alloy/helpers/test/dsl_helpers'
require 'alloy/initializer.rb'
require 'alloy/bridge/compiler'
require 'alloy/bridge/solution'
require 'alloy/bridge/translator'

include Alloy::Dsl

alloy_model :A_M_FST do
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

module A_M_FST
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
    one d.parent && one d.~contents
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
end


class FileSystemTest < Test::Unit::TestCase
  include Alloy::Helpers::Test::DslHelpers
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions
  include Alloy::Bridge

  include A_M_FST

  def setup_class
    Alloy.reset
    Alloy.meta.restrict_to(A_M_FST)
    Alloy.initializer.resolve_fields
    Alloy.initializer.init_inv_fields

    @@als_model = Alloy.meta.to_als
    @@compiler  = Compiler.compile(@@als_model)
    @@sol       = @@compiler.execute_command(0)
  end

  def test
    ans = Alloy.meta.to_als
    assert_equal A_M_FST::Expected_alloy.strip, ans.strip
  end

  def test_file_system_compiler
    a4atoms   = @@sol.all_atoms()

    atoms = Alloy::Bridge::Translator.translate_atoms(a4atoms)
    assert_equal 2, atoms.select{|a| a.instance_of? Name}.size
    assert_equal 1, atoms.select{|a| a.instance_of? File}.size
    assert_equal 1, atoms.select{|a| a.instance_of? Root}.size
    assert_equal 1, atoms.select{|a| a.instance_of? Folder}.size
    assert_equal 3, atoms.select{|a| a.instance_of? Entry}.size
  end

  def test_map
    map = @@sol.field_tuples
    assert_equal 4, map.size
    assert_seq_equal ["name", "contents", "entries", "parent"], map.keys
    assert_equal 3, map["name"].size
    assert_equal 3, map["contents"].size
    assert_equal 3, map["entries"].size
    assert_equal 1, map["parent"].size
  end

  # Expects the following solution:
  #
  #   Root$0
  #     Entry$0: Name$0 -> Folder$0
  #                          Entry$2: Name$1 -> File$0
  #     Entry$1: Name$1 -> Folder$0
  #                          Entry$2: Name$1 -> File$0
  def test_graph
    map   = @@sol.field_tuples
    atoms = Alloy::Bridge::Translator.translate_atoms(@@sol.all_atoms)
    g     = Alloy::Bridge::Translator.recreate_object_graph(map, atoms)
    assert_equal 8, atoms.size
    root0 = g["Root$0"]
    entry1 = g["Entry$1"]
    assert_equal [], g["Root$0"].parent
    assert_set_equal [[g["Entry$0"]], [g["Entry$1"]]], g["Root$0"].entries.unwrap
    assert_equal g["Entry$0"].name, [[g["Name$0"]]]
    assert_equal g["Entry$1"].name, [[g["Name$1"]]]
    assert_equal g["Entry$2"].name, [[g["Name$1"]]]
    assert_equal g["Entry$0"].contents, [[g["Folder$0"]]]
    assert_equal g["Entry$1"].contents, [[g["Folder$0"]]]
    assert_equal g["Entry$2"].contents, [[g["File$0"]]]
    assert_set_equal [[g["Entry$2"]]], g["Folder$0"].entries.unwrap
  end

end
