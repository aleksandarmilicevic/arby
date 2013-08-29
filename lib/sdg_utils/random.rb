module SDGUtils
  module Random

    extend self

    def salted_timestamp(fmt="%s_%s", time_fmt="%s_%L", salt_digits=4)
      time = Time.now.utc.strftime(time_fmt)
      salt = ::Random.rand((10**(salt_digits-1))..(10**salt_digits - 1))
      fmt % [time, salt]
    end

  end
end
