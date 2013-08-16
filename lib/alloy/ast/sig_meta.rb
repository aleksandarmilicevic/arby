require 'alloy/ast/field_meta'

module Alloy
  module Ast

    # ----------------------------------------------------------------------
    # Holds meta information (e.g., fields and their types) about
    # a sig class.
    #
    # @attr sig_cls    [Class <= Sig]
    # @attr subsigs    [Array(Class <= Sig)]
    # @attr fields     [Array(FieldMeta)]
    # @attr inv_fields [Array(FieldMeta)]
    # ----------------------------------------------------------------------
    class SigMeta
      attr_reader :sig_cls, :parent_sig
      attr_reader :abstract, :placeholder
      attr_reader :subsigs
      attr_reader :fields, :inv_fields
      attr_reader :extra

      def initialize(sig_cls, placeholder=false, abstract=false)
        @sig_cls = sig_cls
        @parent_sig = sig_cls.superclass if (sig_cls.superclass.is_sig? rescue nil)
        @placeholder = placeholder
        @abstract = abstract
        @subsigs = []
        @fields = []
        @inv_fields = []
        @extra = {}
      end

      def abstract?;       @abstract end
      def set_abstract;    @abstract = true end
      def placeholder?;    @placeholder end
      def set_placeholder; @placeholder = true end

      def persistent_fields(*args)
        fields(*args).select { |f| f.persistent? }
      end

      def transient_fields(*args)
        fields(*args).select { |f| f.transient? }
      end

      alias_method :pfields, :persistent_fields
      alias_method :tfields, :transient_fields

      def fields(include_inherited=false)
        ret=[] + @fields
        if include_inherited && parent_sig
          ret += parent_sig.meta.fields(true)
        end
        ret
      end

      def inv_fields(include_inherited=false)
        ret=[] + @inv_fields
        if include_inherited && parent_sig
          ret += parent_sig.meta.inv_fields(true)
        end
        ret
      end

      def all_fields(include_inherited=false)
        fields(include_inherited) + inv_fields(include_inherited)
      end

      def add_subsig(subsig_cls)
        @subsigs << subsig_cls
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
        fld = FieldMeta.new opts
        @fields << fld
        fld
      end

      def add_inv_field_for(f)
        full_inv_type = ProductType.new(f.parent.to_atype, f.type).inv
        if full_inv_type.domain.klass != @sig_cls
          raise ArgumentError, "Field #{f} doesn't seem to belong in class #{@sig_cls}"
        end
        # full_inv_type = ProductType.new(f.parent.to_atype, f.type).inv
        # raise ArgumentError if full_inv_type.column(0).cls.klass != @sig_cls
        inv_fld = FieldMeta.new :parent => @sig_cls,
                                :name   => Alloy.conf.inv_field_namer.call(f),
                                :type   => full_inv_type.full_range,
                                :inv    => f,
                                :synth  => true
        # f.set_inv(inv_fld)
        @inv_fields << inv_fld
        inv_fld
      end

      def field(fname, own_only=false)      find_in(fields(!own_only), fname) end
      def field!(fname, own_only=false)     find_in!(fields(!own_only), fname) end
      def [](sym)                           field(sym.to_s) end
      def inv_field(fname, own_only=false)  find_in(inv_fields(!own_only), fname) end
      def inv_field!(fname, own_only=false) find_in!(inv_fields(!own_only), fname) end

      def find_in(fld_ary, fname)
        #TODO cache?
        fld_ary.find {|f| f.name == fname.to_s}
      end

      def find_in!(fld_ary, fname, msg=nil)
        ret = find_in(fld_ary, fname)
        msg = (msg ? msg : "") + "`#{fname}' not found in #{fld_ary.map{|e| e.name}}"
        raise ArgumentError, msg unless ret
        ret
      end

      # Returns type associated with the given field
      #
      # @param fld [String, Symbol]
      # @return [AType]
      def field_type(fname)
        field(fname).type
      end

      # returns a string representation of the field definitions
      def fields_to_alloy; fld_list_to_alloy @fields  end

      # returns a string representation of the synthesized inv field definitions
      def inv_fields_to_alloy; fld_list_to_alloy @inv_fields end

      private

      def fld_list_to_alloy(flds)
        flds.map {|f| "  " + f.to_alloy }
            .join(",\n")
      end
    end

  end
end
