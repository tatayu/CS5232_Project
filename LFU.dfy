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
      |m| <= this.capacity &&
      // minFreq is valid
      ((|m.Keys| > 0 && |freqMap.Keys| > 0) ==> this.minFreq in this.freqMap) &&
      // either both map are empty or both are not
      ((|this.m.Keys| == 0 <==> |this.freqMap.Keys| == 0 )|| (|this.m.Keys| > 0 <==> |this.freqMap.Keys| > 0)) && 
      // for all keys in m, its freq must be in freqMap, and the freqMap[freq] array must contain key
      ((|m.Keys| > 0 && |freqMap.Keys| > 0) ==> forall e :: e in m ==> (m[e].1 in freqMap && e in freqMap[m[e].1])) &&
      // for all keys in m, there should be one and only one set in freqMap contains the key.
      ((|m.Keys| > 0 && |freqMap.Keys| > 0) ==> (forall e, f :: e in m && f in freqMap && m[e].1 != f ==> (e !in freqMap[f]))) &&
      // for all keys in m, it should be in the set of the corresponding frequency in freqMap
      ((|m.Keys| > 0 && |freqMap.Keys| > 0) ==> (forall e, f :: e in m && f in freqMap && m[e].1 == f ==> (e in freqMap[f]))) &&
      // for all keys in m, its frequency must be larger or equal to 1
      ((|m.Keys| > 0 && |freqMap.Keys| > 0) ==> (forall e :: e in m ==> m[e].1 >= 1)) &&


      // for all frequencies in freqMap, their freq set must not be empty
      ((|m.Keys| > 0 && |freqMap.Keys| > 0) ==> (forall e :: e in freqMap ==> |freqMap[e]| > 0)) &&
      // for all frequencies in freqMap, they must be larger or equal to 1
      ((|m.Keys| > 0 && |freqMap.Keys| > 0) ==> (forall e :: e in freqMap ==> e >= 1)) &&
      // for all frequencies in freqMap, they must be belonging to some keys
      ((|m| > 0 && |freqMap| > 0) ==> (forall e :: e in freqMap ==> (exists f :: f in m && m[f].1 == e && f in freqMap[e]))) &&
      // for all sets in freqMap, if a key is not in m, it is in none of the sets
      ((|m.Keys| > 0 && |freqMap.Keys| > 0) ==> (forall e :: e in freqMap ==> (forall nk :: nk !in m ==> nk !in freqMap[e]))) &&
      // for all sets in freqMap, all its elements must be in m
      ((|m.Keys| > 0 && |freqMap.Keys| > 0) ==> (forall e :: e in freqMap ==> (forall k :: k in freqMap[e] ==> k in m))) &&
      // if e's freq is unique, then in freqMap[freq], there should be only 1 element that is e
      // ((|m| > 0 && |freqMap| > 0) ==> (
      //   (forall e, f :: e in m && f in m && e != f && |freqMap[m[e].1]| == 1 ==> (f !in freqMap[m[e].1]) && (m[e].1 != m[f].1)) 
      // )) &&
      ((|m.Keys| > 0 && |freqMap.Keys| > 0) ==> (
        (forall e, f :: e in m && f in m && e != f && (m[e].1 != m[f].1) ==> (e !in freqMap[m[f].1] && f !in freqMap[m[e].1])) 
      )) &&

      // minFreq must be valid
      ((|this.m| > 0 && |this.freqMap| > 0) ==> this.minFreq in this.freqMap && |this.freqMap[this.minFreq]| > 0) &&
      // minFreq must be min
      ((|this.m| > 0 && |this.freqMap| > 0) ==> (forall e :: e in freqMap && e != minFreq ==> minFreq <= e)) &&
      // value must not equal to -1
      ((|this.m| > 0 && |this.freqMap| > 0) ==> (forall k :: k in m.Keys ==> m[k].0 != -1)) 
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

    method MapRemove(oldMap:map<int, (int, int)>, key:int) returns (newMap:map<int, (int, int)>)
      requires |oldMap| > 0;
      requires key in oldMap;
      ensures key !in newMap;
      ensures |newMap| < |oldMap|;
      ensures |newMap| + 1 == |oldMap|;
      ensures oldMap - {key} == newMap;
    {
      ghost var val := oldMap[key];
      var nM := oldMap - {key};
      assert nM[key := val] == oldMap; // Must have!!!
      return nM;
    }

    method FreqMapRemove(oldMap:map<int, set<int>>, key:int) returns (newMap:map<int, set<int>>)
      requires |oldMap| > 0;
      requires key in oldMap;
      ensures key !in newMap;
      ensures |newMap| < |oldMap|;
      ensures |newMap| + 1 == |oldMap|;
      ensures oldMap - {key} == newMap;
    {
      ghost var val := oldMap[key];
      var nM := oldMap - {key};
      assert nM[key := val] == oldMap; // Must have!!!
      return nM;
    }

    //Add element to the last of the array
    method AddElement(oldSet: set<int>, element: int) returns (newSet: set<int>)
      requires element !in oldSet
      ensures |newSet| - |oldSet| == 1
      ensures element in newSet
      ensures forall e :: e in oldSet ==> e in newSet;
      ensures forall e :: e in newSet && e != element ==> e in oldSet;
      ensures newSet - {element} == oldSet;
    {
      var elementSet := {element};
      newSet := oldSet + elementSet;
      return newSet;
    }

    method get(key: int) returns (value: int)
      requires Valid();
      modifies this;
      ensures Valid();
      ensures key !in m.Keys <==> value == -1;
      ensures key in m.Keys <==> value != -1;
      ensures key in old(m) <==> key in m;
      ensures key in old(m) ==> (key in m && value == m[key].0 && old(m[key].1) == (m[key].1 - 1)); // freq should increment
      ensures key in old(m) ==> m[key].0 == old(m[key].0); // no change in value
      ensures |m.Keys| == |old(m.Keys)| // no change in cache size
      ensures forall e :: e in old(m) && e != key ==> e in m && m[e] == old(m[e]); // Other keys do not change
      ensures key in old(m) ==> (old(m[key].1) !in freqMap) || (old(m[key].1) in freqMap && key !in freqMap[old(m[key].1)]); // The old freq should not be in freqMap, or new freqMap[freq] list should no longer contain the key
      ensures key in old(m) ==> (m[key].1 in freqMap && key in freqMap[m[key].1]); // The new freq should be in freqMap, and the key should be in the set of the new freqMap
      ensures key in old(m) ==> forall e :: e in freqMap && e != m[key].1 ==> key !in freqMap[e]; // The key should not be in another other freq set if the freq mismatches
      ensures forall oldKey :: oldKey in old(m) ==> oldKey in m && old(m[oldKey].0) == m[oldKey].0; // The cache key and value does not change.
      ensures old(m) - {key} == m - {key};
      ensures capacity == old(capacity)
      
    {
      // assert (|m| > 0 && |freqMap| > 0) ==> (forall e, f :: e in m && f in m && e != f && m[e].1 != m[f].1 ==> (f !in freqMap[m[e].1]));
      if(key !in m.Keys){
        value := -1;
      }
      else{
        assert(key in m.Keys);
        //update map with new freq
        value := m[key].0;
        var oldFreq := m[key].1;
        var newFreq := oldFreq + 1;
        this.m := this.m[key := (value, newFreq)];

        //remove from old frequency list
        var oldFreqList := this.freqMap[oldFreq];
        assert oldFreqList == freqMap[old(m[key].1)];
        if |oldFreqList| == 1 {

          setUniqness(oldFreqList, key); // Must have!!
          this.freqMap := this.freqMap - {oldFreq};

        } else {
          var newList := Remove(oldFreqList, key);
          assert oldFreqList == newList + {key};
          this.freqMap := this.freqMap[oldFreq := newList];
          assert forall e :: e in freqMap && e != oldFreq ==> old(freqMap[e]) == freqMap[e];
          assert |old(freqMap.Keys)| == |freqMap.Keys|;
          assert forall e :: e in old(freqMap[oldFreq]) && e != key ==> e in freqMap[oldFreq];
        }

        
        //add to new frequency list
        if (newFreq in this.freqMap) {
          var newFreqList := this.freqMap[newFreq];
          assert |newFreqList| > 0;
          var addList := AddElement(newFreqList, key);
          this.freqMap := this.freqMap[newFreq := addList];
        } else {
          var newFreqList := {key};
          this.freqMap := this.freqMap[newFreq := newFreqList];
        }
        //update minFreq
        if(oldFreq == this.minFreq && oldFreq !in freqMap){
          minFreq := minFreq + 1;
          assert minFreq in freqMap;
        }
      }
      return value;
    }
    
    // Must use this to tell Dafny, if a set has only 1 element, and item is in set, then this set == {item}
    lemma setUniqness(s:set<int>, item:int) 
      requires |s| == 1 && item in s;
      ensures s == {item};
    {
      ghost var newS := s - {item};
      assert newS + {item} == s;
    }

     method put(key: int, value: int)
       requires Valid();
       requires value != -1;
        modifies this;
        
        ensures Valid();
        ensures key in m;
        ensures exists e :: e in freqMap && key in freqMap[e];
        
        //key in map
        ensures key in old(m) ==> m[key].0 == value
        ensures key in old(m) ==> |m.Keys| == |old(m.Keys)|
        ensures key in old(m) ==> freqMap == old(freqMap) && minFreq == old(minFreq)
        
        //key not in map and map is empty
        ensures (key !in old(m) && old(|m.Keys|) == 0) ==> |m.Keys| == 1 && m[key].1 == 1
        ensures (key !in old(m) && old(|m.Keys|) == 0) ==> minFreq == 1 && |freqMap.Keys| == 1 && key in freqMap[minFreq] && |freqMap[minFreq]| == 1
        ensures (key !in old(m) && old(|m.Keys|) == 0) ==> {m[key].1} == freqMap.Keys
        
        //key not in map but not full capacity
        ensures (key !in old(m) && 0 < old(|m.Keys|) < capacity) ==> |m.Keys| <= capacity && |m.Keys| == |old(m.Keys)| + 1 && m[key].1 == 1
        ensures (key !in old(m) && 0 < old(|m.Keys|) < capacity) ==> (forall k :: k in old(m) ==> k in m && m[k] == old(m[k]));
        ensures (key !in old(m) && 0 < old(|m.Keys|) < capacity) ==>  minFreq == 1 && |freqMap.Keys| >= 1 && key in freqMap[minFreq] && |freqMap[minFreq]| >= 1
        ensures (key !in old(m.Keys) && 0 < old(|m.Keys|) < capacity) ==> forall f :: f in old(freqMap) ==> f in freqMap
        
        //key not in map and full capacity
        ensures (key !in old(m.Keys) && old(|m.Keys|) == capacity) ==> |m.Keys| == capacity && m[key].1 == 1
        ensures (key !in old(m.Keys) && old(|m.Keys|) == capacity) ==>  minFreq == 1 && |freqMap.Keys| >= 1 && key in freqMap[minFreq] && |freqMap[minFreq]| >= 1
        // ensures (key !in old(m.Keys) && old(|m.Keys|) == capacity) ==> exists k :: forall f:: k in old(m.Keys) && f in freqMap.Keys ==> k !in m.Keys && k !in freqMap[f]
        ensures (key !in old(m.Keys) && old(|m.Keys|) == capacity) ==> exists k :: k in old(m) && k in old(freqMap[minFreq]) && k !in m && (forall f :: f in freqMap ==> k !in freqMap[f]);
     {
       if(key in m) { //key in m && |this.freqMap| > 0 && |this.m| >0 0
         var freq := m[key].1;
         //update map with new value
         m := m[key := (value, freq)];
       } 
       else{
        assert key !in m;
         //cache is full
         if(|this.m| == this.capacity){
           var oldLFUList := this.freqMap[this.minFreq];
          
           //update freq by removing the LFU element
           var LFUElement :| LFUElement in oldLFUList;
          
           // if only 1 element left in oldFLUList, remove from freqMap
           if(|oldLFUList| == 1){
             setUniqness(oldLFUList, LFUElement);
             this.freqMap := FreqMapRemove(this.freqMap, this.minFreq);
           }
           else{
             
             var newLFUList := Remove(oldLFUList, LFUElement);
             this.freqMap := this.freqMap[this.minFreq := newLFUList];
           }
           //update map by removing the LFU element
           assert LFUElement in m;
           this.m := MapRemove(this.m, LFUElement);
           assert |m| < |old(m)|;
         }
        assert |this.m| < this.capacity;
          
         //update map by putting the new element
         this.m := this.m[key := (value, 1)];
          
         //update freq
         if(1 in this.freqMap){
           var LFUListOne := this.freqMap[1];
           var newLFUListOne := AddElement(LFUListOne, key);
           this.freqMap := this.freqMap[1 := newLFUListOne];
         }
         else{
           this.freqMap := this.freqMap[1 := {key}];
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