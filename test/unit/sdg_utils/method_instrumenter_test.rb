require 'my_test_helper.rb'
require 'sdg_utils/proxy.rb'

module SDGUtils

  class MethodInstrumenterTest < Test::Unit::TestCase
    # def test0
    #   a = [1, 2, 3]
    #   SDGUtils::MethodInstrumenter.before_object_methods(a){|name|
    #     puts "called: #{name}"
    #   }
    #   a.size
    # end

    def test1
      a = [1, 2, 3]
      SDGUtils::MethodInstrumenter.around_object_methods(a){|name,args,block,&cont|
        puts "called: #{name}"
        cont.call
      }
      puts a.size
    end

  end

end
