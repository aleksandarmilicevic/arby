require 'sdg_utils/meta_utils'

module Alloy
  module Ast

    module Checks
      def check_iden(id, kind="")
        msg = "#{kind} must be either string or symbol"
        raise ArgumentError, msg unless String === id || Symbol === id
        msg = "`#{id}' (#{kind}) is not a valid identifier"
        raise ArgumentError, msg unless SDGUtils::MetaUtils.check_identifier(id)
      end
    end

  end
end
