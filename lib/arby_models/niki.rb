require 'arby/arby_dsl'

module ArbyModels
  extend Arby::Dsl

  alloy :NikiExample do
    sig Person [
      name: String,
      age: Int,
      friends: (set Person)
    ] do
      fun inc[i: Int][Int] {
        return i + 1
      }
    end

    sig Student < Person do
      fun inc[i: Int][Int] {
        return i + 2
      }
    end
  end

end
