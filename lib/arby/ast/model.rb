require 'arby/bridge/solver_helpers'
require 'arby/arby_conf'
require 'arby/ast/types'
require 'arby/resolver'
require 'arby/utils/codegen_repo'
require 'sdg_utils/caching/searchable_attr'

module Arby
  module Ast

    class Model
      include Arby::Bridge::SolverHelpers
      include SDGUtils::Caching::SearchableAttr

      attr_reader :scope_module, :ruby_module, :name, :relative_name

      def initialize(scope_module, ruby_module)
        @scope_module = scope_module
        @ruby_module = ruby_module
        @name = scope_module.name
        @relative_name = @name.split("::").last
        @resolved = false
        @sig_builders = []

        init_searchable_attrs
      end

      attr_searchable :sig, :fun, :pred, :assertion, :procedure, :fact, :command, :run

      def all_funs() funs + preds + assertions + facts end
      def checks() commands.select{|c| c.check?} end
      def runs()   commands.select{|c| c.run?} end

      def to_als()
        require 'arby/utils/alloy_printer'
        Arby::Utils::AlloyPrinter.export_to_als(self)
      end

      private

      def add_sig_builder(sb)
        @sig_builders << sb
      end

      def resolve
        return if @resolved
        resolve_fields
        init_inv_fields
        eval_sig_bodies
        # add getters for all fields
        flds = self.sigs.map{|s| s.meta.fields + s.meta.inv_fields}.flatten
        flds.each do |fld|
          Arby::Utils::CodegenRepo.module_eval_method @ruby_module, fld.getter_sym,
          <<-RUBY, __FILE__, __LINE__+1
def #{fld.getter_sym}
  #{fld.parent.name}.#{fld.getter_sym}
end
RUBY
        end
        @resolved = true
      end

      # ----------------------------------------------------------------
      # Goes through all the fields, searches for
      # +UnresolvedRefColType+, resolves them and updates the field
      # information.
      # ----------------------------------------------------------------
      def resolve_fields
        logger = Arby.conf.logger
        flds = self.sigs.map{|s| s.meta.fields}.flatten
        funs = self.sigs.map{|s| s.meta.funs + s.meta.preds}.flatten + self.all_funs
        types = flds.map(&:type) + funs.map(&:full_type)

        types.each do |type|
          type.each do |utype|
            col_type = utype.cls
            if col_type.instance_of? Arby::Ast::UnaryType::ColType::UnresolvedRefColType
              logger.debug "[resolve_fields]   trying to resolve #{col_type}..."
              cls = Arby::Resolver.resolve_type(col_type)
              if cls
                logger.debug "[resolve_fields]     resolved to #{cls}"
                utype.update_cls(cls)
              else
                logger.debug "[resolve_fields]     unable to resolve #{col_type}"
              end
            end
          end
        end
      end

      # ----------------------------------------------------------------
      # Creates inverse fields for the user-defined fields.
      # ----------------------------------------------------------------
      def init_inv_fields(force=false)
        logger = Arby.conf.logger
        self.sigs.each do |r|
          r.meta.pfields.each do |f|
            unless f.inv
              logger.debug "[init_inv_fields] checking field #{f}"
              range_cls = f.type.range.cls.klass rescue Object
              if range_cls < Arby::Ast::ASig
                logger.debug "[init_inv_fields]   defining inverse of #{f}"
                invfld = range_cls.send(:_add_inv_for_field, f)
                logger.debug "[init_inv_fields]     #{invfld} defined"
              end
            end
          end
        end
      end

      # ----------------------------------------------------------------
      # Goes throug all the fields, searches for +UnresolvedRefColType+,
      # resolves them and updates the field information.
      # ----------------------------------------------------------------
      def eval_sig_bodies(force=false)
        return unless Arby.conf.defer_body_eval
        @sig_builders.each(&:eval_body_now!)
        @sig_builders = []
      end

    end
  end
end
