require 'logger'
require 'nilio'
require 'sdg_utils/config'

module Arby

  def self.default_symexe_conf
    SDGUtils::Config.new do |c|
      c.convert_missing_fields_to_joins = false
      c.convert_missing_methods_to_fun_calls = true
    end
  end

  def self.default_alloy_printer_conf
    SDGUtils::Config.new do |c|
      c.sig_namer = lambda{|sig| sig.relative_name}
      c.fun_namer = lambda{|fun| fun.name}
      c.arg_namer = lambda{|fld| fld.name}
    end

    # SDGUtils::Config.new do |c|
    #   c.sig_namer = lambda{|sig| sig.name.gsub /:/, "_"}
    #   c.sig_namer = lambda{|sig| sig.relative_name}
    #   c.fun_namer = lambda{|fun| "#{c.sig_namer[fun.owner]}__#{fun.name}"}
    #   c.fun_namer = lambda{|fun| fun.name}
    #   c.arg_namer = lambda{|fld| "#{c.sig_namer[fld.owner]}__#{fld.name}"}
    # end

  end

  # Options
  #   :inv_field_namer [Proc(fld)]
  #   :logger          [Logger]
  def self.default_conf
    SDGUtils::Config.new do |c|
      c.inv_field_namer                    = lambda { |fld| "inv_#{fld.name}" }
      c.turn_methods_into_funs             = true
      c.allow_undef_vars                   = true
      c.allow_undef_consts                 = true
      c.defer_body_eval                    = true
      c.detect_appended_facts              = true
      c.wrap_field_values                  = true
      c.generate_methods_for_global_fields = true
      c.typecheck                          = true
      c.sym_exe                            = default_symexe_conf
      c.logger                             = Logger.new(NilIO.instance)
      c.alloy_printer                      = default_alloy_printer_conf
    end
  end
end
