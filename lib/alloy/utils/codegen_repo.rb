require 'ostruct'

module Alloy
module Utils

  module CodegenRepo
    class << self

      @@gen_code = []
      def gen_code() @@gen_code end

      def get_code_for_target(target)
        @@gen_code.select{|e|
          e.target == target || e.desc.target == target
        }.map{|e|
          e.code
        }
      end

      # --------------------------------------------------------------
      #
      # Evaluates a source code block (`src') in the context of a
      # module (`mod'), and remembers it for future reference.
      #
      # @param mod [Module]  - module to add code to
      # @param src [String]  - source code to be evaluated for module
      #                        `mod'
      # @param file [String] - optional file name of the source
      # @param line [String] - optional line number in the source file
      #                        source code
      # @param desc [Hash]   - arbitrary hash to be stored alongside
      #
      # --------------------------------------------------------------
      def eval_code(mod, src, file=nil, line=nil, desc={})
        # Red.conf.log.debug "------------------------- in #{mod}"
        # Red.conf.log.debug src
        __append :kind => :eval_code, :target => mod, :code => src, :desc => desc
        mod.class_eval src, file, line
      end

      # --------------------------------------------------------------
      #
      # Evaluates a source code block (`src') in the context of a
      # module (`mod'), and remembers it for future reference.
      #
      # @param code [String]   - arbitrary code
      # @param target [Object] - optional target
      # @param desc [Hash]     - arbitrary hash to be stored alongside
      #
      # --------------------------------------------------------------
      def record_code(code, target=nil, desc={})
        __append :kind => :code, :target => target, :code => code, :desc => desc
      end

      private

      def __append(hash)
        hash[:desc] = OpenStruct.new(hash[:desc])
        @@gen_code << OpenStruct.new(hash)
      end

    end
  end

end
end
