class LFUCache {

    var capacity : int;
    var minFreq : int;
    var m : map<int, (int, int)>; //key -> {value, freq}
    var freqMap: map<int, set<int>>; //freq -> set of keys

    constructor(capacity: int)
      requires 4 >= capacity > 0;
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
      4 >= this.capacity > 0 
      && this.minFreq >= 0 && 
      // |freqMap.Keys| <= |m| <= this.capacity &&
      // minFreq is valid
      ((|m| > 0 && |freqMap| > 0) ==> this.minFreq in this.freqMap) &&
      // either both map are empty or both are not
      ((|this.m| == 0 <==> |this.freqMap| == 0 )|| (|this.m| > 0 <==> |this.freqMap| > 0)) && 
      // for all keys in m, its freq must be in freqMap, and the freqMap[freq] array must contain key
      ((|m| > 0 && |freqMap| > 0) ==> forall e :: e in m ==> (m[e].1 in freqMap && e in freqMap[m[e].1])) &&
      // for all keys in m, there should be one and only one set in freqMap contains the key.
      ((|m| > 0 && |freqMap| > 0) ==> (forall e, f :: e in m && f in freqMap && m[e].1 != f ==> (e !in freqMap[f]))) &&
      // for all keys in m, it should be in the set of the corresponding frequency in freqMap
      ((|m| > 0 && |freqMap| > 0) ==> (forall e, f :: e in m && f in freqMap && m[e].1 == f ==> (e in freqMap[f]))) &&


      // for all frequencies in freqMap, their freq set must not be empty
      ((|m| > 0 && |freqMap| > 0) ==> (forall e :: e in freqMap ==> |freqMap[e]| > 0)) &&
      // for all frequencies in freqMap, they must be belonging to some keys
      ((|m| > 0 && |freqMap| > 0) ==> (forall e :: e in freqMap ==> (exists f :: f in m && m[f].1 == e && f in freqMap[e]))) &&
      // for all sets in freqMap, if a key is not in m, it is in none of the sets
      ((|m| > 0 && |freqMap| > 0) ==> (forall e :: e in freqMap ==> (forall nk :: nk !in m ==> nk !in freqMap[e]))) &&
      // for all sets in freqMap, all its elements must be in m
      ((|m| > 0 && |freqMap| > 0) ==> (forall e :: e in freqMap ==> (forall k :: k in freqMap[e] ==> k in m))) &&
      // if e's freq is unique, then in freqMap[freq], there should be only 1 element that is e
      // ((|m| > 0 && |freqMap| > 0) ==> (
      //   (forall e, f :: e in m && f in m && e != f && |freqMap[m[e].1]| == 1 ==> (f !in freqMap[m[e].1]) && (m[e].1 != m[f].1)) 
      // )) &&
      ((|m| > 0 && |freqMap| > 0) ==> (
        (forall e, f :: e in m && f in m && e != f && (m[e].1 != m[f].1) ==> (e !in freqMap[m[f].1] && f !in freqMap[m[e].1])) 
      )) &&
      // for all sets in freqMap, if all of their size is 1, then it means the size of m == size of freqMap, and vice versa
      // ((|m| > 0 && |freqMap| > 0) ==> (
      //   (exists e :: e in freqMap && |freqMap[e]| > 1 <==> |m| > |freqMap.Keys| )
      // )) &&
      // (forall a, b :: a in m && b in m ==> a !=b) &&

      // minFreq must be valid
      ((|this.m| > 0 && |this.freqMap| > 0) ==> this.minFreq in this.freqMap && |this.freqMap[this.minFreq]| > 0) &&
      // minFreq must be min
      ((|this.m| > 0 && |this.freqMap| > 0) ==> (forall e :: e in freqMap && e != minFreq ==> minFreq <= e))
    } 
    
    //Remove element by a given value
    method Remove(oldSet: set<int>, element: int) returns (newSet: set<int>)
      requires |oldSet| > 0
      requires element in oldSet
      ensures |oldSet| - |newSet| == 1
      ensures element !in newSet
      ensures forall e :: e in newSet ==> e in oldSet;
      ensures forall e :: e in oldSet && e != element ==> e in newSet;
      ensures forall e :: e !in oldSet ==> e !in newSet;
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
      ensures forall e :: e in newSet && e != element ==> e in oldSet;
    {
      var elementSet := {element};
      newSet := oldSet + elementSet;
      return newSet;
    }

    method get(key: int) returns (value: int)
      requires Valid();
      // requires |this.freqMap| > 0 ==> exists e :: e in this.freqMap && key in this.freqMap[e];
      // requires |this.freqMap| > 0 ==> key in this.m && key in this.freqMap[this.m[key].1];
      // requires |this.freqMap| > 0 ==> key in this.m && (this.m[key].1 + 1 !in this.freqMap || key !in this.freqMap[this.m[key].1 + 1]);
      modifies this;
      ensures Valid();
      ensures key !in m ==> value == -1;
      ensures key in old(m) ==> (key in m && value == m[key].0 && old(m[key].1) == (m[key].1 - 1)); // freq should increment
      ensures key in old(m) ==> m[key].0 == old(m[key].0); // no change in value
      ensures |m| == |old(m)| // no change in cache size
      ensures forall e :: e in old(m) && e != key ==> e in m && m[e] == old(m[e]); // Other keys do not change
      ensures key in old(m) ==> (old(m[key].1) !in freqMap) || (old(m[key].1) in freqMap && key !in freqMap[old(m[key].1)]); // The old freq should not be in freqMap, or new freqMap[freq] list should no longer contain the key
      ensures key in old(m) ==> (m[key].1 in freqMap && key in freqMap[m[key].1]); // The new freq should be in freqMap, and the key should be in the set of the new freqMap
      ensures key in old(m) ==> forall e :: e in freqMap && e != m[key].1 ==> key !in freqMap[e]; // The key should not be in another other freq set if the freq mismatches
      ensures forall oldKey :: oldKey in old(m) ==> oldKey in m && old(m[oldKey].0) == m[oldKey].0; // The cache key and value does not change.
      // DO NOT need to check freqMap[freq+1] constains the key, as it is ensured by "ensures Valid(); && ensures key in m;" above.
    {
      // assert (|m| > 0 && |freqMap| > 0) ==> (forall e, f :: e in m && f in m && e != f && m[e].1 != m[f].1 ==> (f !in freqMap[m[e].1]));
      if(key !in m){
        value := -1;
      }
      else{
        //update map with new freq
        // assert exists e :: e in freqMap && |freqMap[e]| > 1 <==> |m| > |freqMap.Keys|;
        value := m[key].0;
        var oldFreq := m[key].1;
        var newFreq := oldFreq + 1;
        this.m := this.m[key := (value, newFreq)];

        //remove from old frequency list
        var oldFreqList := this.freqMap[oldFreq];
        assert oldFreqList == freqMap[old(m[key].1)];
        if |oldFreqList| == 1 {
          // assert exists e :: e in freqMap && |freqMap[e]| > 1 <==> |m| > |freqMap.Keys|;
          // assert |freqMap| <= |m|;
          setUniqness(oldFreqList, key);
          this.freqMap := this.freqMap - {oldFreq};
          // assert forall e :: e in freqMap && |old(freqMap[e])| > 1 ==> |freqMap[e]| > 1; // this is necessary for next assert to be proven
          // assert exists e :: e in freqMap && |freqMap[e]| > 1 <==> |m| > |freqMap.Keys|;
          // assert |freqMap.Keys| < |m|;
        } else {
          // assert exists e :: e in freqMap && |freqMap[e]| > 1 <==> |m| > |freqMap.Keys|;
          var newList := Remove(oldFreqList, key);
          assert oldFreqList == newList + {key};
          // assert forall e :: e in oldFreqList && e != key ==> e in newList;
          // assert forall e :: e in newList ==> e in m.Keys;
          // assert |newList| == 1 ==> (forall e, f :: e in newList && f in m.Keys && e != f ==> f !in newList);
          this.freqMap := this.freqMap[oldFreq := newList];
          assert forall e :: e in freqMap && e != oldFreq ==> old(freqMap[e]) == freqMap[e];
          assert |old(freqMap.Keys)| == |freqMap.Keys|;
          // assert |freqMap.Keys| < |m|;
          assert forall e :: e in old(freqMap[oldFreq]) && e != key ==> e in freqMap[oldFreq];
          // assert exists e :: e in freqMap && |freqMap[e]| > 1 <==> |m| > |freqMap.Keys|;
        }

        
        //add to new frequency list
        if (newFreq in this.freqMap) {
          // assert exists e :: e in freqMap && |freqMap[e]| > 1 <==> |m| > |freqMap.Keys|;
          var newFreqList := this.freqMap[newFreq];
          assert |newFreqList| > 0;
          // assert |freqMap.Keys| < |m|;
          var addList := AddElement(newFreqList, key);
          this.freqMap := this.freqMap[newFreq := addList];
          // assert |freqMap.Keys| < |m|;
          // assert forall e :: e in old(freqMap) && |old(freqMap[e])| > 1 ==> |freqMap[e]| > 1; // this is necessary for next assert to be proven
          // assert exists e :: e in freqMap && |freqMap[e]| > 1 <==> (|m| > |freqMap.Keys|);
        } else {
          // assert |freqMap.Keys| < |m|;
          var newFreqList := {key};
          //  assert exists e :: e in freqMap && |freqMap[e]| > 1 <==> |m| > |freqMap.Keys|;
          this.freqMap := this.freqMap[newFreq := newFreqList];
          // assert forall e :: e in old(freqMap) && |old(freqMap[e])| > 1 ==> |freqMap[e]| > 1; // this is necessary for next assert to be proven
          // assert exists e :: e in freqMap && |freqMap[e]| > 1 <==> (|m| > |freqMap.Keys|);
        }
        // assert forall e :: e in freqMap && |freqMap[e]| == 1 <==> (|m| == |freqMap.Keys|);
        //update minFreq
        if(oldFreq == this.minFreq && oldFreq !in freqMap){
          minFreq := minFreq + 1;
          assert minFreq in freqMap;
        }
        // assert forall e :: e in m ==> (m[e].1 in freqMap && e in freqMap[m[e].1]);
        // assert forall e, f :: e in m && f in m && e != f && |freqMap[m[e].1]| == 1 ==> (f !in freqMap[m[e].1]);
      }
      // assert forall e :: (e in this.m && e != key && this.m[e].1 != this.m[key].1) ==> e !in this.freqMap[this.m[key].1];
      return value;
    }
    
    lemma setUniqness(s:set<int>, item:int) 
      requires |s| == 1 && item in s;
      ensures s == {item};
    {
      ghost var newS := s - {item};
      assert newS + {item} == s;
    }

    // lemma mapEquality(m1:map<int, (int, int)>, m2:map<int, set<int>>)
    //   requires |m1| > 0 && |m2| > 0;
    //   requires forall e :: e in m1 ==> (m1[e].1 in m2 && e in m2[m1[e].1]);
    //   requires forall e :: e !in m1 ==> (forall f :: f in m2 ==> e !in m2[f]);
    //   requires forall e, f :: e in m1 && f in m2 && m1[e].1 != f ==> (e !in m2[f]);
    //   requires forall e, f :: e in m1 && f in m2 && m1[e].1 == f ==> (e in m2[f]);
    //   requires forall e :: e in m2 ==> |m2[e]| > 0;
    //   requires forall e :: e in m2 ==> (exists f :: f in m1 && m1[f].1 == e && f in m2[e]);
    //   requires forall e :: e in m2 ==> (forall nk :: nk !in m1 ==> nk !in m2[e]);
    //   requires forall e :: e in m2 ==> (forall k :: k in m2[e] ==> k in m1);
    //   ensures exists e :: e in m2 && |m2[e]| > 1 <==> |m| > |m2|;

    // {
    //   assert forall e,f :: e in m1 && f in m2 && e != f && 
    // }
    
     method put(key: int, value: int)
       requires Valid();
       requires (key in m) ==> (|freqMap| > 0 && |m| > 0)
       requires (key !in m && |freqMap| > 0 && |m| > 0) ==> minFreq in freqMap
       requires |this.freqMap| > 0 && |this.m| > 0 ==> this.minFreq in this.freqMap && |freqMap[minFreq]| > 0
       requires |this.freqMap| > 0 ==> forall e :: e in this.freqMap ==> |this.freqMap[e]| > 0;
       requires |this.freqMap| > 0 ==> exists e :: e in this.freqMap && key in this.freqMap[e];
       requires |this.freqMap| > 0 ==> key in this.m && key in this.freqMap[this.m[key].1];
       requires |this.freqMap| > 0 ==> this.minFreq in freqMap
       modifies this
       ensures Valid();
       
       ensures forall oldkey :: (oldkey in old(m) && |old(m)| > 0 && |old(freqMap)| > 0) ==> oldkey in m && m[oldkey].1 in freqMap && oldkey in freqMap[m[oldkey].1]
       ensures (key in old(m)) ==> key in m && m[key].0 == value && old(minFreq) == minFreq
       ensures (key in old(m)) ==> (m[key].0 == value);

        ensures (key !in old(m) && |old(m)| < capacity) ==> (forall oldKey :: oldKey in old(m) ==> (m[oldKey].0 == old(m[oldKey].0) && m[oldKey].1 == old(m[oldKey].1)))
        ensures (key !in old(m) && |old(m)| < capacity) ==> (forall oldKey :: oldKey in old(m) ==>oldKey in freqMap[m[oldKey].1])
        ensures (key !in old(m) && |old(m)| < capacity) ==> (key in m && m[key].0 == value && m[key].1 == 1 && |m| <= capacity && |m| == |old(m)| + 1);
        ensures (key !in old(m) && |old(m)| < capacity) ==> (minFreq == 1);
        ensures (key !in old(m) && |old(m)| == capacity) ==> (key in m && m[key].0 == value && m[key].1 == 1 && |m| == capacity);
        ensures (key !in old(m) && |old(m)| == capacity) ==> (minFreq == 1);
     {
       
       var val := get(key);
       
       if(val != -1){ //key in m && |this.freqMap| > 0 && |this.m| >0 0
         assert (key in m &&|m| > 0 && |freqMap| > 0);
         assert (key !in m || |m| == 0 || |freqMap| == 0);
         var freq := this.m[key].1;
         //update map with new value
         this.m := this.m[key := (value, freq)];
         //assert (old(minFreq) == minFreq);
         
       } 
       else{
        assert(minFreq in freqMap);
         //cache is full
         if(|this.m| == this.capacity){
          
           var oldLFUList := this.freqMap[this.minFreq];
          
           //update freq by removing the LFU element
           var LFUElement :=  multiset(oldLFUList)[0];
          
           // if only 1 element left in oldFLUList, remove from freqMap
           if(|oldLFUList| == 1){
             this.freqMap := this.freqMap - {this.minFreq};
           }
           else{
             
             var newLFUList := Remove(oldLFUList, LFUElement);
             this.freqMap := this.freqMap[this.minFreq := newLFUList];
           }
           //update map by removing the LFU element
           this.m := this.m - {LFUElement};
         }

         //update map by putting the new element
         this.m := this.m + map[key := (value, 1)];

         //update freq
         if(1 in this.freqMap){
           var LFUListOne := this.freqMap[1];
           var newLFUListOne := AddElement(LFUListOne, key);
           this.freqMap := this.freqMap[1 := newLFUListOne];
         }
         else{
           this.freqMap := this.freqMap + map[1 := {key}];
         }
        
         //update minFreq
         this.minFreq := 1;
       }
       
     }
 }

 method Main()
 {
   var LFUCache := new LFUCache(2);
   LFUCache.put(1,1);
   assert((|LFUCache.m| == 0 <==> |LFUCache.freqMap| == 0) || (|LFUCache.m| > 0 <==> |LFUCache.freqMap| > 0));
   LFUCache.put(2,2);
   var val := LFUCache.get(1);
   print val;
   LFUCache.put(3,3);
 }