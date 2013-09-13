require 'my_test_helper'
require 'alloy/helpers/test/dsl_helpers'
require 'alloy/initializer.rb'

include Alloy::Dsl

# dir_cls = Object.send :remove_const, :Dir
# file_cls = Object.send :remove_const, :File

alloy_model :A_M_FST do
  sig Name
  abstract sig Obj

  sig Entry [
    name: Name,
    contents: Obj
  ]

  sig (Folder < Obj) [
    entries: (set Entry),
    parent: (lone Folder)
  ]

  sig :File < Folder {
    some d: Folder do
      self.in? d.entries.contents
    end
  }

  one sig Root < Folder {
    no parent
  }

  lone sig Curr < Folder
end

# Object.send :const_set, :Dir, dir_cls
# Object.send :const_set, :File, file_cls

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
    # ans = A_M_ABT.delUndoesAdd
    # puts "#{ans}"
    # puts "-----------"
    # ans = A_M_ABT.delUndoesAdd_alloy
    # puts "#{ans}"
    puts Alloy.meta.to_als
  end
end
