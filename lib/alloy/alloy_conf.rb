require 'logger'
require 'nilio'
require 'sdg_utils/config'

module Alloy

  # Options
  #   :inv_field_namer [Proc(fld)]
  #   :logger          [Logger]
  def self.default_conf
    SDGUtils::Config.new do |c|
      c.inv_field_namer = lambda { |fld| "inv_#{fld.name}" }
      c.logger          = Logger.new(NilIO.instance)
    end
  end
end
