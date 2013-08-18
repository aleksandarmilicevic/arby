require 'sdg_utils/meta_utils'
require 'sdg_utils/event/events'

module Alloy
  extend self

  module Model

    module MMUtils
      module Static
        protected

        # Returns plural of the given noun by
        #  (1) replacing the trailing 'y' with 'ies', if `word'
        #      ends with 'y',
        #  (2) appending 'es', if `word' ends with 's'
        #  (3) appending 's', otherwise
        def pl(word)
          word = word.to_s
          if word[-1] == "y"
            word[0...-1] + "ies"
          elsif word[-1] == "s"
            word + "es"
          else
            word + "s"
          end
        end

        # Generates several methods for each symbol in `whats'.  For
        # example, if whats == [:sig] it generates:
        #
        #   private
        #   def _sigs()          _restrict @sigs end
        #
        #   public
        #   def sigs()           _sigs end
        #   def sig_created(obj) add_to(@sigs, obj) end
        #   def get_sig(name)    _cache(_sigs, name) end
        #   def get_sig!(name)   get_sig(name) || fail "sig `#{name}' not found" end
        #   def find_sig(name)   _search_by_name(_sigs, name) end
        #
        #   alias_method :sig, :get_sig
        #   alias_method :sig!, :get_sig!
        def gen(*whats)
          whats.each do |what|
            self.class_eval <<-RUBY, __FILE__, __LINE__+1
  private
  def _#{pl what}()        _restrict @#{pl what} end

  public
  def #{pl what}()         _#{pl what} end
  def #{what}_created(obj) add_to(@#{pl what}, obj) end
  def get_#{what}(name)    _cache(_#{pl what}, name) end
  def get_#{what}!(name)   get_#{what}(name) || fail("#{what} `\#{name}' not found") end
  def find_#{what}(name);  _search_by_name(_#{pl what}, name) end

  alias_method :#{what}, :get_#{what}
  alias_method :#{what}!, :get_#{what}!
            RUBY
          end
        end
      end

      # ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

      def self.included(base)
        base.extend(Alloy::Model::MMUtils::Static)
      end

      def clear_restriction
        restrict_to nil
      end

      def restrict_to(mod)
        @restriction_mod = mod
      end

      protected

      def _cache(col, name, cache_var=@cache)
        cache_var[name] ||= _find_by_name(col, name)
      end

      def _restrict(src)
        return src unless @restriction_mod
        src.select {|e|
          e.name && e.name.start_with?(@restriction_mod.to_s + "::")}
      end

      def _find_by_name(col, name)
        col.find {|e| e.name == name}
      end

      def _search_by_name(col, name)
        return nil unless name
        col.find {|e| e.relative_name == name.relative_name}
      end
    end

    # ==================================================================
    # == Class +MetaModel+
    # ==================================================================
    class MetaModel
      include MMUtils
      include SDGUtils::Events::EventProvider

      def initialize
        reset
      end

      def reset
        @models = []
        @sigs = []
        @restriction_mod = nil
        @cache = {}
      end

      gen :model, :sig

      def open_model(mod)
        @opened_model =
          case mod
          when String, Symbol
            model!(mod.to_s)
          when Alloy::Ast::Model
            mod
          else
            raise ArgumentError, "#{mod}:#{mod.class} is neither String nor Model"
          end
      end

      def close_model(mod)
        msg = "#{mod} is not the currently opened model"
        raise ArgumentError, msg unless @opened_model == mod
        @opened_model = nil
      end

      private

      def add_to(col, val) col << val end
    end

  end
end
