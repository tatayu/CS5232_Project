class LFUCache {

    var capacity : int;
    var minFreq : int;
    var m : map<int, (int, int)>; //key -> {value, freq}
    var freqMap: map<int, set<int>>; //freq -> set of keys

     constructor(capacity: int)
        requires capacity >= 0;
        ensures Valid();
    {
      this.capacity := capacity;
      this.minFreq := 0;
      this.m := map[];
      this.freqMap := map[];
    }

    predicate Valid()
      reads this;
      // reads this.freqMap.Values;
    {
      // general value check
      this.capacity >= 0 && this.minFreq >= 0 && 
      ((|m| > 0 && |freqMap| > 0) ==> this.minFreq in this.freqMap) &&
      // either both map are empty or both are not
      (|this.m| == 0 <==> |this.freqMap| == 0 || (|this.m| > 0 <==> |this.freqMap| > 0)) && 
      // for all keys in m, its freq must be in freqMap, and the freqMap[freq] array must contain key
      ((|m| > 0 && |freqMap| > 0) ==> forall e :: e in m ==> (m[e].1 in freqMap && e in freqMap[m[e].1])) &&
      // for all keys in m, there should be one and only one set in freqMap contains the key.
      ((|m| > 0 && |freqMap| > 0) ==> (forall e, f :: e in m && f in m && e != f && m[e].1 != m[f].1 ==> (f !in freqMap[m[e].1]))) &&
      ((|m| > 0 && |freqMap| > 0) ==> (forall e, f :: e in m && f in freqMap && m[e].1 != f ==> (e !in freqMap[f])))
    } 
    
    //Remove element by a given value
    method Remove(oldSet: set<int>, element: int) returns (newSet: set<int>)
      requires |oldSet| > 0
      requires element in oldSet
      ensures |oldSet| - |newSet| == 1
      ensures element !in newSet
      ensures forall e :: e in newSet ==> e in oldSet;
    {
      var elementSet := {element};
      newSet := oldSet - elementSet;
      return newSet;
    }

    //Add element to the last of the array
    method AddElement(oldSet: set<int>, element: int) returns (newSet: set<int>)
      requires element !in oldSet
      ensures |newSet| - |oldSet| == 1
      ensures element in newSet
      ensures forall e :: e in oldSet ==> e in newSet;
    {
      var elementSet := {element};
      newSet := oldSet + elementSet;
      return newSet;
    }

    method get(key: int) returns (value: int)
      requires Valid();
      requires |this.freqMap| > 0 ==> forall e :: e in m ==> m[e].1 in freqMap;
      requires |this.freqMap| > 0 ==> forall e :: e in this.freqMap ==> |this.freqMap[e]| > 0;
      requires |this.freqMap| > 0 ==> exists e :: e in this.freqMap ==> key in this.freqMap[e];
      requires |this.freqMap| > 0 ==> key in this.m && key in this.freqMap[this.m[key].1];
      requires |this.freqMap| > 0 ==> key in this.m && (this.m[key].1 + 1 !in this.freqMap || key !in this.freqMap[this.m[key].1 + 1]);
      modifies this;
      ensures Valid();
      ensures key !in m ==> value == -1;
      ensures key in old(m) ==> (key in m && value == m[key].0 && old(m[key].1) == (m[key].1 - 1)); // freq should increment
      ensures key in old(m) ==> (old(m[key]).1 !in freqMap) || (old(m[key]).1 in freqMap && key !in freqMap[old(m[key]).1]); // The freq should not in freqMap, or freqMap[freq] list should no longer contain the key
      // ensures forall oldKey :: oldKey in old(m) && oldKey in m && old(m[oldKey].0) == m[oldKey].0; // The cache key and value does not change.
      // DO NOT need to check freqMap[freq+1] constains the key, as it is ensured by "ensures Valid(); && ensures key in m;" above.
    {
      assert (|m| > 0 && |freqMap| > 0) ==> forall e :: e in m ==> (m[e].1 in freqMap && e in freqMap[m[e].1]);
      assert (|m| > 0 && |freqMap| > 0) ==> (forall e, f :: e in m && f in m && e != f && m[e].1 != m[f].1 ==> (f !in freqMap[m[e].1]));
      if(key !in m || |this.freqMap| == 0 || |this.m| == 0){
        value := -1;
      }
      else{
        //update map with new freq
        assert forall e :: e in m ==> (m[e].1 in freqMap && e in freqMap[m[e].1]);
        assert forall e :: (e in this.m  && e != key) ==> (this.m[e].1 in this.freqMap); // others are not affected
        value := m[key].0;
        var oldFreq := m[key].1;
        assert key in this.freqMap[oldFreq];
        var newFreq := oldFreq + 1;
        assert (old(this.m[key].1) == this.m[key].1);
        this.m := this.m[key := (value, newFreq)];
        assert (oldFreq == m[key].1 - 1);
        assert this.m[key].1 == newFreq;
        assert old(this.m[key].1) == newFreq - 1;
        assert old(this.m[key].1) == oldFreq;
        assert old(this.m[key].1) == (this.m[key].1 - 1);
        assert forall e :: (e in this.m && e != key) ==> (this.m[e].1 in this.freqMap);
        assert forall e :: (e in this.m && e != key && this.m[e].1 == this.m[key].1) ==> e in this.freqMap[this.m[key].1];
        assert (|m| > 0 && |freqMap| > 0) ==> (forall e, f :: e in m && f in m && e != f && m[e].1 != m[f].1 ==> (f !in freqMap[m[e].1]));
        assert forall e :: (e in this.m && e != key && this.m[e].1 != this.m[key].1) ==> e !in this.freqMap[this.m[key].1];

        //remove from old frequency list
        var oldFreqList := this.freqMap[oldFreq];
        if |oldFreqList| == 1 {
          assert forall e :: (e in this.m && e != key && this.m[e].1 == this.m[key].1) ==> e in this.freqMap[this.m[key].1];
          assert forall e :: (e in this.m && e != key && this.m[e].1 != this.m[key].1) ==> e !in this.freqMap[this.m[key].1];
          assert forall e :: (e in this.m && e != key) ==> (this.m[e].1 in this.freqMap);
          assert |oldFreqList| == 1 && key in oldFreqList && forall e :: (e in this.m  && e != key) ==> (e !in oldFreqList); // Whyyyy?
          assert oldFreq in this.freqMap;
          assert key in this.freqMap[oldFreq];
          assert old(this.m[key].1) in this.freqMap;
          assert |this.freqMap[old(this.m[key].1)]| == 1;
          assert forall e :: (e in this.m  && e != key) ==> this.m[e].1 != oldFreq;
          this.freqMap := this.freqMap - {oldFreq};
          assert oldFreq !in this.freqMap;
          // assert forall e :: (e in this.m  && e != key) ==> (this.m[e].1 in this.freqMap);
        } else {
          assert forall e :: (e in this.m  && e != key) ==> (this.m[e].1 in this.freqMap);
          assert oldFreq in this.freqMap;
          assert key in oldFreqList;
          var removeList := Remove(oldFreqList, key);
          assert key !in removeList;
          assert forall e :: e in removeList ==> e in oldFreqList;
          this.freqMap := this.freqMap[oldFreq := removeList];
          assert key !in this.freqMap[oldFreq];
        }
        // assert forall e :: (e in this.m  && e != key) ==> (this.m[e].1 in this.freqMap);
        
        //add to new frequency list
        if (newFreq in this.freqMap) {
          var newFreqList := this.freqMap[newFreq];
          assert key !in this.freqMap[newFreq];
          var addList := AddElement(newFreqList, key);
          this.freqMap := this.freqMap[newFreq := addList];
        } else {
          var newFreqList := {key};
          this.freqMap := this.freqMap[newFreq := newFreqList];
          
        }
        assert key in this.freqMap[newFreq];
        assert this.m[key].1 in this.freqMap;
        // assert forall e :: e in this.m ==> (this.m[e].1 in this.freqMap);

        //update minFreq
        if(oldFreq == this.minFreq){
          minFreq := minFreq + 1;
        }

        // assert forall e :: e in this.m ==> (this.m[e].1 in this.freqMap);
        // assert forall e :: e in this.m ==> (this.m[e].1 in this.freqMap && e in this.freqMap[m[e].1]);
      }
      return value;
    }
    
    
    method put(key: int, value: int)
    {
      var val := get(key);
      if(key in m && val != -1){
        var freq := m[key].1;
        //update map with new value
        m := m[key := (value, freq)];
        return;
      }
      else{
        //cache is full
        if(|m| == capacity){
          var oldLFUList := freqMap[minFreq];
          
          //update freq by removing the LFU element
          //TODO: check the number of element in oldFLUList. If only got 1, remove key from freq
          var temp : multiset<int> := multiset(oldLFUList);
          var LFUElement := temp[0];
          var newLFUList := Remove(oldLFUList, LFUElement);
          freqMap := freqMap[minFreq := newLFUList];

          //update map by removing the LFU element
          m := m - {LFUElement};
        }

        //update map by putting the new element
        var new_m : map<int, (int, int)>;
        new_m := new_m[key := (value, 1)];
        m := m + new_m;

        //update freq
        //TODO: check if freq[1] exists. If not, create one
        var LFUListOne := freqMap[1];
        var newLFUListOne := AddElement(LFUListOne, key);
        freqMap := freqMap[1 := newLFUListOne];

        //update minFreq
        minFreq := 1;
      }
    }
}

method Main()
{
  var LFUCache := new LFUCache(2);
  LFUCache.put(1,1);
  LFUCache.put(2,2);
  var val := LFUCache.get(1);
  print val;
  LFUCache.put(3,3);
}