require 'alloy/alloy_meta'
require 'alloy/alloy_conf'
require 'alloy/resolver.rb'

module Alloy

  # =================================================================
  # Class +CInitializer+
  #
  # Performs various initialization tasks. 
  #
  # Options:
  #   :resolver  - resolver to use, defaults to +Alloy::Resolver+
  #   :baseklass - base class for types for which to add inverse
  #                fields, defaults to +Alloy::Ast::Sig+.
  # =================================================================
  class CInitializer
    RESOLVER_OPT = :resolver
    BASEKLASS_OPT = :baseklass

    @@resolved  = false
    @@added_inv = false

    attr_reader :options

    def initialize(hash={})
      opt = hash.clone
      opt[RESOLVER_OPT] ||= Alloy::Resolver
      opt[BASEKLASS_OPT] ||= Alloy::Ast::Sig
      @options = opt
    end

    # ----------------------------------------------------------------
    # Initializes everything.
    # ----------------------------------------------------------------
    def init_all
      resolve_fields
      init_inv_fields
      deep_freeze
    end

    # ----------------------------------------------------------------
    # Goes throug all the fields, searches for +UnresolvedRefColType+,
    # resolves them and updates the field information.
    # ----------------------------------------------------------------
    def resolve_fields(force=false)
      return unless force || Alloy.test_and_set(:fields_resolved)

      logger = Alloy.conf.logger
      Alloy.meta.sigs.each do |s|
        s.meta.fields.each do |f|
          logger.debug "[resolve_fields] checking field #{f}"
          f.type.each do |utype|
            col_type = utype.cls
            if col_type.instance_of? Alloy::Ast::UnaryType::ColType::UnresolvedRefColType
              logger.debug "[resolve_fields]   trying to resolve #{col_type}..."
              cls = @options[RESOLVER_OPT].resolve_type!(col_type)
              logger.debug "[resolve_fields]     resolved to #{cls}"
              utype.update_cls(cls)
            end
          end
        end
      end
    end
    
    # ----------------------------------------------------------------
    # Creates inverse fields for the user-defined fields. 
    # ----------------------------------------------------------------
    def init_inv_fields(force=false)
      return unless force || Alloy.test_and_set(:inv_fields_added) 

      logger = Alloy.conf.logger
      Alloy.meta.sigs.each do |r|
        r.meta.pfields.each do |f|
          unless f.inv
            logger.debug "[init_inv_fields] checking field #{f}"
            range_cls = f.type.range.cls.klass
            if range_cls < @options[BASEKLASS_OPT]
              logger.debug "[init_inv_fields]   defining inverse of #{f}"
              invfld = range_cls.send(:_add_inv_for_field, f)
              logger.debug "[init_inv_fields]     #{invfld} defined"
            end
          end
        end
      end
    end

    # ----------------------------------------------------------------
    # Freezes most of the meta stuff. 
    # ----------------------------------------------------------------
    def deep_freeze
      sig_metas = Alloy.meta.sigs.map{|r| r.meta}
      fld_metas = sig_metas.map{|s| s.fields + s.inv_fields}.flatten
      [Alloy.conf, Alloy.meta, *sig_metas, *fld_metas].each{|e| e.freeze}
    end
  end

end
