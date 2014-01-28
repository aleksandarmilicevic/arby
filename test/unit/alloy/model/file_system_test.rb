require 'my_test_helper'
require 'arby_models/file_system'
require 'alloy/helpers/test/dsl_helpers'
require 'alloy/initializer.rb'
require 'alloy/bridge/compiler'
require 'alloy/bridge/solution'

class FileSystemTest < Test::Unit::TestCase
  include Alloy::Helpers::Test::DslHelpers
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions
  include Alloy::Bridge

  include ArbyModels::FileSystem

  def setup_class
    Alloy.reset
    Alloy.meta.restrict_to(ArbyModels::FileSystem)
    Alloy.initializer.resolve_fields
    Alloy.initializer.init_inv_fields

    @@als_model = Alloy.meta.to_als
    @@compiler  = Compiler.compile(@@als_model)
    @@sol       = @@compiler.execute_command(0)
  end

  def test
    ans = Alloy.meta.to_als
    assert_equal_ignore_whitespace ArbyModels::FileSystem::Expected_alloy, ans
  end

  def test_file_system_compiler
    atoms   = @@sol.translate_atoms()

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
    inst = @@sol.translate_to_arby
    assert_equal 8, inst.size
    root0 = inst["Root$0"]
    entry1 = inst["Entry$1"]
    assert_equal [], inst["Root$0"].parent
    assert_set_equal [[inst["Entry$0"]], [inst["Entry$1"]]], inst["Root$0"].entries.unwrap
    assert_equal inst["Entry$0"].name, [[inst["Name$0"]]]
    assert_equal inst["Entry$1"].name, [[inst["Name$1"]]]
    assert_equal inst["Entry$2"].name, [[inst["Name$1"]]]
    assert_equal inst["Entry$0"].contents, [[inst["Folder$0"]]]
    assert_equal inst["Entry$1"].contents, [[inst["Folder$0"]]]
    assert_equal inst["Entry$2"].contents, [[inst["File$0"]]]
    assert_set_equal [[inst["Entry$2"]]], inst["Folder$0"].entries.unwrap
  end

  def test_correct_check
    sol = @@compiler.execute_command(1)
    assert !sol.satisfiable?
  end

end
