require 'arby_models/alloy_sample/systems/__init'
require 'arby_models/alloy_sample/util/relation'

module ArbyModels::AlloySample::Systems
  # =================================================================
  # Model of views in object-oriented programming.
  #
  # Two object references, called the view and the backing, are
  # related by a view mechanism when changes to the backing are
  # automatically propagated to the view. Note that the state of a
  # view need not be a projection of the state of the backing; the
  # keySet method of Map, for example, produces two view
  # relationships, and for the one in which the map is modified by
  # changes to the key set, the value of the new map cannot be
  # determined from the key set. Note that in the iterator view
  # mechanism, the iterator is by this definition the backing object,
  # since changes are propagated from iterator to collection and not
  # vice versa. Oddly, a reference may be a view of more than one
  # backing: there can be two iterators on the same collection, eg. A
  # reference cannot be a view under more than one view type.
  #
  # A reference is made dirty when it is a backing for a view with
  # which it is no longer related by the view invariant.  This usually
  # happens when a view is modified, either directly or via another
  # backing. For example, changing a collection directly when it has
  # an iterator invalidates it, as does changing the collection
  # through one iterator when there are others.
  #
  # More work is needed if we want to model more closely the failure
  # of an iterator when its collection is invalidated.
  #
  # As a terminological convention, when there are two complementary
  # view relationships, we will give them types t and t'. For example,
  # KeySetView propagates from map to set, and KeySetView' propagates
  # from set to map.
  #
  # @author: Daniel Jackson
  # @translated_by: Aleksandar Milicevic
  # =================================================================
  alloy :Views do
    open ArbyModels::AlloySample::Util::Relation

    sig Ref
    sig Object

    # t->b->v in views when v is view of type t of backing b
    # dirty contains refs that have been invalidated
    ordered sig State [
      refs: (set Ref),
      obj: refs ** (one Object),
      views: ViewType ** refs ** refs,
      dirty: (set refs)
   ]

    sig Map extends Object [
      keys: (set Ref),
      map: keys ** (one Ref)
    ] {
      all(s: State){ (keys + Ref.(map)).in? s.refs }
    }
    sig MapRef extends Ref do
      pred keySet[pre, post: State, setRefs: SetRef] {
        post.obj[setRefs].(elts) == dom(map[pre.obj[this]]) and
        modifies(pre, post, none) and
        allocates(pre, post, setRefs) and
        post.views == pre.views + (KeySetView**this**setRefs) + 
                                  (KeySetView_**setRefs**this)
      }

      pred put[pre, post: State, k: Ref, v: Ref] {
        map[post.obj[this]] == map[pre.obj[this]].merge(k**v) and
        modifies(pre, post, this) and
        allocates(pre, post, none) and
        post.views == pre.views
      }
    end

    fact { State.(obj)[MapRef].in? Map }

    sig Iterator extends Object [
      left, done: (set Ref),
      lastRef: (lone done)
    ] {
      all(s: State){ (done + left + lastRef).in? s.refs }
    }
    sig IteratorRef extends Ref do
      pred remove[pre, post: State] {
        let(i: pre.obj[this], i_: post.obj[this]) {
          left[i_] == left[i] and
          done[i_] == done[i] - lastRef[i] and
          no lastRef[i_]
        } and
        modifies(pre,post,this)
        allocates(pre, post, none)
        pre.views == post.views
      }

      pred :next[pre, post: State, ref: Ref] {
        let(i: pre.obj[this], i_: post.obj[this]) {
          ref.in? left[i] and
          left[i_] == left[i] - ref and
          done[i_] == done[i] + ref and
          lastRef[i_] == ref
        } and
        modifies(pre, post, this) and
        allocates(pre, post, none) and
        pre.views == post.views
      }

      pred hasNext[s: State] {
        some left[s.obj[this]]
      }
    end

    fact { State.(obj)[IteratorRef].in? Iterator}

    sig Set extends Object [
      elts: (set Ref)
    ] { 
      all(s: State){ elts.in? s.refs }
    }

    sig SetRef extends Ref do
      pred iterator[pre, post: State, iterRef: IteratorRef] {
        let(i: post.obj[iterRef]) {
          i.left == elts[pre.obj[this]] and
          no i.done + i.lastRef
        } and
        modifies(pre, post, none)
        allocates(pre, post, iterRef)
        post.views == pre.views + (IteratorView**iterRef**this)
      }
    end

    fact { State.(obj)[SetRef].in? Set }

    abstract sig ViewType 
    one sig KeySetView, KeySetView_, IteratorView < ViewType
    fact viewTypes {
      State.(views)[KeySetView].in? MapRef ** SetRef and
      State.(views)[KeySetView_].in? SetRef ** MapRef and
      State.(views)[IteratorView].in? IteratorRef ** SetRef and
      all(s: State){ s.views[KeySetView] == ~(s.views[KeySetView_]) }
    }

    # mods is refs modified directly or by view mechanism doesn_t
    # handle possibility of modifying an object and its view at once?
    # should we limit frame conds to non-dirty refs?
    pred modifies[pre, post: State, rs: (set Ref)] {
      let(vr: pre.views[ViewType]) { 
        let(mods: (rs.*vr)) {
          all(r: pre.refs - mods){ pre.obj[r] == post.obj[r] } and
          all(b: mods, v: pre.refs, t: ViewType) {
            if (b**v).in? pre.views[t] 
              viewFrame(t, pre.obj[v], post.obj[v], post.obj[b])
            end
          } and
          post.dirty == pre.dirty + pre.refs.select{ |b|
            some(v: Ref, t: ViewType) {
              (b**v).in? pre.views[t] and
              !viewFrame(t, pre.obj[v], post.obj[v], post.obj[b])
            }
          }
        }
      }
    }
    
    pred allocates[pre, post: State, rs: (set Ref)] {
      no rs & pre.refs and
      post.refs == pre.refs + rs
    }

    # models frame condition that limits change to view object from v to
    # v_ when backing object changes to b_
    pred viewFrame[t: ViewType, [:v, :v_, :b_] => Object] {
      (if t.in? KeySetView   then elts[v_] == dom(map[b_]) end) and
      (if t.in? KeySetView_  then elts[b_] == dom(map[v_]) end) and
      (if t.in? KeySetView_  then elts[b_].<(map[v]) == elts[b_].<(map[v_]) end) and
      (if t.in? IteratorView then elts[v_] == left[b_] + done[b_] end)
    }

    assertion zippishOK {
      all(ks, vs: SetRef, m: MapRef, [:ki, :vi] => IteratorRef, [:k, :v] => Ref) {
        let(s0: State::first) {
          let(s1: State::next[s0]) {
            let(s2: State::next[s1]) {
              let(s3: State::next[s2]) {
                let(s4: State::next[s3]) {
                  let(s5: State::next[s4]) {
                    let(s6: State::next[s5]) {
                      let(s7: State::next[s6]) {
                        if precondition(s0, ks, vs, m) and
                            no s0.dirty and
                            ks.iterator(s0, s1, ki) and
                            vs.iterator(s1, s2, vi) and
                            ki.hasNext(s2) and
                            vi.hasNext(s2) and
                            ki.next(s2, s3, k) and
                            vi.next(s3, s4, v) and
                            m.put(s4, s5, k, v) and
                            ki.remove(s5, s6) and
                            vi.remove(s6, s7) 
                          no State.dirty
                        end
                      }}}}}}}}}
    }

    pred precondition[pre: State, [:ks, :vs, :m] => Ref] {
      # all these conditions and other errors discovered in scope of 6 but 8,3
      # in initial state, must have view invariants hold
      all(t: ViewType, [:b, :v] => pre.refs) {
        if (b**v).in? pre.views[t]
          viewFrame(t, pre.obj[v], pre.obj[v], pre.obj[b])
        end
      }
      # sets are not aliases
      #   ks != vs
      # sets are not views of map
      #   no (ks+vs)**m & ViewType.pre.views
      # no iterator currently on either set
      #   no Ref**(ks+vs) & ViewType.pre.views
    }

    check :zippishOK, 6, State => 8, ViewType => 3 # expect fail

    # experiment with controlling heap size
    fact { all(s: State){ s.obj.size < 5 } }

  end
end
