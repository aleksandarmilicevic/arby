require 'alloy/ast/field'
require 'alloy/ast/fun'

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
      attr_reader :sig_cls, :parent_sig
      attr_reader :abstract, :placeholder
      attr_reader :subsigs
      attr_reader :fields, :inv_fields
      attr_reader :preds, :funs
      attr_reader :extra

      def initialize(sig_cls, placeholder=false, abstract=false)
        @sig_cls     = sig_cls
        @parent_sig  = sig_cls.superclass if (sig_cls.superclass.is_sig? rescue nil)
        @placeholder = placeholder
        @abstract    = abstract
        @subsigs     = []
        @fields      = []
        @inv_fields  = []
        @preds       = []
        @funs        = []
        @extra       = {}
      end

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

      def fields(w_inherited=false)     fetch_attr(:fields, w_inherited) end
      def inv_fields(w_inherited=false) fetch_attr(:inv_fields, w_inherited) end
      def preds(w_inherited=false)      fetch_attr(:preds, w_inherited) end
      def funs(w_inherited=false)       fetch_attr(:funs, w_inherited) end

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

      def add_fun(fun_opts, is_pred=false)
        opts = normalize_fun_opts(fun_opts)
        cstr, store = is_pred ? [:pred, @preds] : [:fun, @funs]
        fun = Fun.send cstr, opts
        store << fun
        fun
      end
      def add_pred(fun_opts) add_fun(fun_opts, true) end

      def fun(fun_name, own_only=false)   find_in(@funs, own_only) end
      def pred(pred_name, own_only=false) find_in(@preds, own_only) end

      def add_field(fld_name, fld_type, hash={})
        opts = hash.merge :parent => sig_cls,
                          :name   => fld_name.to_s,
                          :type   => fld_type
        fld = Field.new opts
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
        inv_fld = Field.new :parent => @sig_cls,
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

      def fetch_attr(name, include_inherited=false)
        ret = if include_inherited && parent_sig
                parent_sig.meta.fetch_attr(name, true)
              else
                []
              end
        ret += instance_variable_get "@#{name}"
      end

      def find_in(fld_ary, fname)
        #TODO cache?
        fld_ary.find {|f| f.name == fname.to_s}
      end

      def find_in!(fld_ary, fname, msg=nil)
        ret = find_in(fld_ary, fname)
        msg = (msg ? msg : "") + "`#{fname}' not found in #{fld_ary.map(&:name)}"
        raise ArgumentError, msg unless ret
        ret
      end

      def fld_list_to_alloy(flds)
        flds.map {|f| "  " + f.to_alloy }
            .join(",\n")
      end

      protected

      def normalize_fun_opts(fun_opts)
        case fun_opts
        when Hash
          fun_opts
        when Fun
          fun_opts.to_opts
        else
          msg = "Expected either Hash or Fun, got #{fun_opts}:#{fun_opts.class}"
          raise ArgumentError, msg
        end.merge({
          :parent => sig_cls
        })
      end
    end

  end
end
