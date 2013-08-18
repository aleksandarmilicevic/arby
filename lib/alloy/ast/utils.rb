require 'alloy/dsl/fun_builder'
require 'sdg_utils/meta_utils'

module Alloy
  module Ast

    module Checks
      def check_iden(id, kind="")
        check_name = proc{ |name|
          msg = "`#{name}' (#{kind}) is not a valid identifier"
          ok = SDGUtils::MetaUtils.check_identifier(name)
          raise ArgumentError, msg unless ok
          ok
        }
        case id
        when String, Symbol
          check_name[id]
        when Alloy::Dsl::FunBuilder
          if id.in_init?
            check_name[id.name]
          else
            msg = "partially built function (#{id}) is not a valid identifier (#{kind})"
            raise ArgumentError, msg
          end
        else
          raise ArgumentError, "#{kind} must be in [String, Symbol] but is #{id.class}"
        end
      end
    end

  end
end
