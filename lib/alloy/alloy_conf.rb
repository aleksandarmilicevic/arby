require 'logger'
require 'nilio'
require 'sdg_utils/config'

module Alloy

  # Options
  #   :inv_field_namer [Proc(fld)]
  #   :logger          [Logger]
  def self.default_conf
    SDGUtils::Config.new do |c|
      c.inv_field_namer        = lambda { |fld| "inv_#{fld.name}" }
      c.turn_methods_into_funs = true
      c.allow_undef_vars       = true
      c.allow_undef_consts     = true
      c.logger                 = Logger.new(NilIO.instance)
    end
  end
end
