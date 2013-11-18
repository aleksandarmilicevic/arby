require 'logger'
require 'nilio'
require 'sdg_utils/config'

module Alloy

  def self.default_symexe_conf
    SDGUtils::Config.new do |c|
      c.convert_missing_fields_to_joins = false
      c.convert_missing_methods_to_fun_calls = true
    end
  end

  # Options
  #   :inv_field_namer [Proc(fld)]
  #   :logger          [Logger]
  def self.default_conf
    SDGUtils::Config.new do |c|
      c.inv_field_namer        = lambda { |fld| "inv_#{fld.name}" }
      c.turn_methods_into_funs = true
      c.allow_undef_vars       = true
      c.allow_undef_consts     = true
      c.defer_body_eval        = true
      c.detect_appended_facts  = true
      c.sym_exe                = default_symexe_conf
      c.logger                 = Logger.new(NilIO.instance)
    end
  end
end
