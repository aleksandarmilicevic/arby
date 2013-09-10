require 'alloy/ast/field'
require 'alloy/ast/fun'
require 'sdg_utils/caching/searchable_attr'

module Alloy
  module Ast

    # ----------------------------------------------------------------------
    # Holds meta information (e.g., fields and their types) about
    # a sig class.
    #
    # @attr sig_cls    [Class <= Sig]
    # @attr subsigs    [Array(Class <= Sig)]
    # @attr fields     [Array(Field)]
    # @attr inv_fields [Array(Field)]
    # ----------------------------------------------------------------------
    class SigMeta
      include SDGUtils::Caching::SearchableAttr

      attr_reader :sig_cls, :parent_sig
      attr_reader :abstract, :placeholder
      attr_reader :extra

      attr_hier_searchable :subsig, :field, :inv_field, :fun, :pred

      def initialize(sig_cls, placeholder=false, abstract=false)
        @sig_cls     = sig_cls
        @parent_sig  = sig_cls.superclass if (sig_cls.superclass.is_sig? rescue nil)
        @placeholder = placeholder
        @abstract    = abstract
        @extra       = {}
        init_searchable_attrs(SigMeta)
      end

      def all_funs()    funs + preds end
      def any_fun(name) all_funs.find{|f| f.name.to_s == name.to_s} end

      def _hierarchy_up() parent_sig && parent_sig.meta end

      def abstract?()       @abstract end
      def set_abstract()    @abstract = true end
      def placeholder?()    @placeholder end
      def set_placeholder() set_abstract; @placeholder = true end

      def persistent_fields(*args)
        fields(*args).select { |f| f.persistent? }
      end

      def transient_fields(*args)
        fields(*args).select { |f| f.transient? }
      end

      alias_method :pfields, :persistent_fields
      alias_method :tfields, :transient_fields

      def all_fields(include_inherited=false)
        fields(include_inherited) + inv_fields(include_inherited)
      end

      def all_subsigs
        @subsigs.map {|s| [s] << s.all_subsigs}.flatten
      end

      def all_supersigs
        if parent_sig
          [parent_sig] + parent_sig.meta.all_supersigs
        else
          []
        end
      end

      def oldest_ancestor(ignore_abstract=false, ignore_placeholder=true)
        if parent_sig
          parent_sig.oldest_ancestor(ignore_abstract) ||
            begin
              if ignore_placeholder && parent_sig.placeholder?
                nil
              elsif ignore_abstract && parent_sig.abstract?
                nil
              else
                parent_sig
              end
            end
        else
          nil
        end
      end

      def add_field(fld_name, fld_type, hash={})
        opts = hash.merge :parent => sig_cls,
                          :name   => fld_name.to_s,
                          :type   => fld_type
        fld = Field.new opts
        @fields << fld
        unless sig_cls.respond_to?(fld_name.to_sym)
          sig_cls.class_eval <<-RUBY, __FILE__, __LINE__+1
            def self.#{fld_name.to_s}() get_cls_field(#{fld_name.to_s.inspect}) end
          RUBY
        end
        fld
      end

      def add_inv_field_for(f)
        full_inv_type = ProductType.new(f.parent.to_atype, f.type).inv
        if full_inv_type.domain.klass != @sig_cls
          raise ArgumentError, "Field #{f} doesn't seem to belong in class #{@sig_cls}"
        end
        inv_fld = Field.new :parent => @sig_cls,
                            :name   => Alloy.conf.inv_field_namer.call(f),
                            :type   => full_inv_type.full_range,
                            :inv    => f,
                            :synth  => true
        @inv_fields << inv_fld
        inv_fld
      end

      def [](sym) field(sym.to_s) end

      # Returns type associated with the given field
      #
      # @param fld [String, Symbol]
      # @return [AType]
      def field_type(fname)
        field(fname).type
      end

      # returns a string representation of the field definitions
      def fields_to_alloy() fld_list_to_alloy @fields  end

      # returns a string representation of the synthesized inv field definitions
      def inv_fields_to_alloy() fld_list_to_alloy @inv_fields end

      def fld_list_to_alloy(flds)
        flds.map {|f| "  " + f.to_alloy }
            .join(",\n")
      end

    end

  end
end
