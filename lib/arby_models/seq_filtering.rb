require 'alloy/alloy_dsl'

Alloy.conf.sym_exe.convert_missing_fields_to_joins = true

module ArbyModels
  extend Alloy::Dsl

  alloy_model :SeqFiltering do
    sig A [
      x: Int
    ] {
      x == 2 || x == 4
    }

    fun prevOccurrences[s: (seq A), idx: Int][set Int] {
      s.indsOf(s[idx]).select{|i| i < idx}
    }

    pred filter[s: (seq A), ans: (seq A)] {
      filtered = s.elems.select{|a| a.x < 3}
      
      s.size == 4 and
      ans.elems == filtered and
      all(a: filtered) { ans.a.size == s.a.size } and
      all(i1: s.inds, i2: s.inds) {
        if i2 > i1 && filtered.contains?(s[i1] + s[i2])
          some(ii1: ans.inds, ii2: ans.inds) {
            ii2 > ii1 and
            ans[ii1] == s[i1] and
            ans[ii2] == s[i2] and
            prevOccurrences(s, i1) == prevOccurrences(ans, ii1) and
            prevOccurrences(s, i2) == prevOccurrences(ans, ii2)
          }
        end
      }
    }

    run :filter, "for 4"
  end


end
