require 'my_test_helper'
require_relative 'compiler_test'

module Arby
  module Bridge

    class CompilerOOTest < CompilerTest

      # @override
      def setup_class
        @@compiler = Compiler.compile(nil, @@model)
        @@solution = @@compiler.execute_command(0)
      end

      protected

      # @override
      def get_all_atoms()  @@solution._a4sol.getAllAtoms end
      # @override
      def get_all_fields() @@compiler.all_fields end

    end

  end
end
