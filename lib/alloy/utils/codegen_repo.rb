require 'sdg_utils/obj/uninstantiable'

module Alloy
module Utils

  class CodegenRepo
    include SDGUtils::Obj::Uninstantiable

    class << self

      @@gen_code = []
      def gen_code() @@gen_code end

      # --------------------------------------------------------------
      #
      # Evaluates a source code block (`src') in the context of a
      # module (`mod'), and remembers it for future reference.
      #
      # @param mod [Module]  - module to add code to
      #
      # @param src [String]  - source code to be evaluated for module
      #                        `mod'
      #
      # @param file [String] - optional file name of the source
      #
      # @param line [String] - optional line number in the source file
      #                        source code
      #
      # @param desc [Hash]   - arbitrary hash to be stored alongside
      #
      # --------------------------------------------------------------
      def eval_code(mod, src, file=nil, line=nil, desc={})
        # Red.conf.log.debug "------------------------- in #{mod}"
        # Red.conf.log.debug src
        @@gen_code << {:module => mod, :code => src}.merge!(desc)
        mod.class_eval src, file, line
      end

    end
  end

end
end
