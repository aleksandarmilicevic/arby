require 'my_test_helper'
require 'arby_models/file_system'
require 'arby/helpers/test/dsl_helpers'
require 'arby/initializer.rb'
require 'arby/bridge/compiler'
require 'arby/bridge/solution'
require 'arby/ast/tuple_set'

class FileSystemTest < Test::Unit::TestCase
  include Arby::Helpers::Test::DslHelpers
  include SDGUtils::Testing::SmartSetup
  include SDGUtils::Testing::Assertions
  include Arby::Bridge

  include ArbyModels::FileSystem

  def setup_class
    Arby.reset
    Arby.meta.restrict_to(ArbyModels::FileSystem)

    @@als_model = Arby.meta.to_als
    @@compiler  = ArbyModels::FileSystem.compile()
    @@sol       = @@compiler.execute_command(0)
  end

  def assert_ts_equal(ts1, *tuples)
    assert_equal Arby::Ast::TupleSet.wrap(ts1), Arby::Ast::TupleSet.wrap(tuples)
  end

  def test
    ans = Arby.meta.to_als
    # assert_equal_ignore_whitespace ArbyModels::FileSystem::Expected_alloy, ans
  end

  def test_instance
    inst = @@sol.instance

    # assert_equal 2, inst.atoms.select{|a| a.instance_of? Name}.size
    # assert_equal 1, inst.atoms.select{|a| a.instance_of? File}.size
    # assert_equal 1, inst.atoms.select{|a| a.instance_of? Root}.size
    # assert_equal 1, inst.atoms.select{|a| a.instance_of? Dir}.size
    # assert_equal 3, inst.atoms.select{|a| a.instance_of? Entry}.size

    flds = [Entry.meta.field("name"), Entry.contents, Dir.entries, Dir.parent]
    fld_names = flds.map(&:alloy_name)
    assert_set_equal fld_names, inst.fields

    # !non-det!
    # assert_equal 3, inst.field(fld_names[0]).size
    # assert_equal 3, inst.field(fld_names[1]).size
    # assert_equal 3, inst.field(fld_names[2]).size
    # assert_equal 1, inst.field(fld_names[3]).size
  end

  # Expects the following solution:
  #
  #   Root$0
  #     Entry$0: Name$0 -> Dir$0
  #                          Entry$2: Name$1 -> File$0
  #     Entry$1: Name$1 -> Dir$0
  #                          Entry$2: Name$1 -> File$0
  # !non-det!
  def __test_graph
    inst = @@sol.arby_instance

    assert_equal 2, inst.atoms.select{|a| a.instance_of? Name}.size
    assert_equal 1, inst.atoms.select{|a| a.instance_of? File}.size
    assert_equal 1, inst.atoms.select{|a| a.instance_of? Root}.size
    assert_equal 1, inst.atoms.select{|a| a.instance_of? Dir}.size
    assert_equal 3, inst.atoms.select{|a| a.instance_of? Entry}.size

    assert_equal 8, inst.atoms.size
    root0 = inst["Root$0"]
    entry1 = inst["Entry$1"]
    assert_set_equal [], inst["Root$0"].parent
    assert_ts_equal inst["Root$0"].entries, inst["Entry$0"], inst["Entry$1"]
    assert_ts_equal inst["Entry$0"].name, inst["Name$0"]
    assert_ts_equal inst["Entry$1"].name, inst["Name$1"]
    assert_ts_equal inst["Entry$2"].name, inst["Name$1"]
    assert_ts_equal inst["Entry$0"].contents, inst["Dir$0"]
    assert_ts_equal inst["Entry$1"].contents, inst["Dir$0"]
    assert_ts_equal inst["Entry$2"].contents, inst["File$0"]
    assert_ts_equal inst["Dir$0"].entries, inst["Entry$2"]
  end

  def test_correct_check
    sol = @@compiler.execute_command(1)
    assert !sol.satisfiable?
  end

end
