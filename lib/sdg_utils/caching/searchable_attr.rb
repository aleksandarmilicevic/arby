require 'sdg_utils/caching/cache'

module SDGUtils
  module Caching

    module SearchableAttr
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
        #   def _sig_cache()     @sig_cache ||= Cache.new "sig", :fast => true end
        #   def _sig_fnd_cache() @sig_fnd_cache ||= Cache.new "sig_find", :fast => true end
        #
        #   public
        #   def sigs()         _sigs end
        #   def add_sig(obj)   _add_to(@sigs, obj) end
        #   def get_sig(key)   _sig_cache.fetch(key)     {_get_by(_sigs, key)} end
        #   def find_sig(key)  _sig_fnd_cache.fetch(key) {_find_by(_sigs, key)} end
        #   def get_sig!(key)  get_sig(name) || fail "sig `#{name}' not found" end
        #
        #   alias_method :sig, :get_sig
        #   alias_method :sig!, :get_sig!
        def gen(*whats)
          whats.each do |what|
            self.class_eval <<-RUBY, __FILE__, __LINE__+1
  private
  def _#{pl what}()      _restrict @#{pl what} end
  def _#{what}_cache()
    @#{what}_cache ||= SDGUtils::Caching::Cache.new "#{what}", :fast => true
  end
  def _#{what}_fnd_cache()
    @#{what}_fnd_cache ||= SDGUtils::Caching::Cache.new "#{what}_find", :fast => true
  end

  public
  def #{pl what}()       _#{pl what} end
  def add_#{what}(obj)   _add_to(@#{pl what}, obj) end
  def get_#{what}(key)   _#{what}_cache.fetch(key)    { _get_by(_#{pl what}, key) } end
  def find_#{what}(key)  _#{what}_fnd_cache.fetch(key){ _find_by(_#{pl what}, key) } end
  def get_#{what}!(key)  get_#{what}(key) || fail("#{what} `\#{key}' not found") end

  alias_method :#{what}, :get_#{what}
  alias_method :#{what}!, :get_#{what}!
            RUBY
          end
        end
      end

      # ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

      def self.included(base)
        base.extend(Static)
      end

      protected

      def _restrict(src)
        return src
      end

      def _add_to(col, elem)
        col << elem
      end

      def _get_by(col, key)
        col.find {|e| e.name == key}
      end

      def _find_by(col, key)
        return nil unless key
        col.find {|e| e.name == key}
      end
    end

  end
end
