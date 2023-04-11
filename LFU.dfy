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
      ((|this.m| == 0 <==> |this.freqMap| == 0 )|| (|this.m| > 0 <==> |this.freqMap| > 0)) && 
      // for all keys in m, its freq must be in freqMap, and the freqMap[freq] array must contain key
      ((|m| > 0 && |freqMap| > 0) ==> forall e :: e in m ==> (m[e].1 in freqMap && e in freqMap[m[e].1])) &&
      // for all keys in m, there should be one and only one set in freqMap contains the key.
      ((|m| > 0 && |freqMap| > 0) ==> (forall e, f :: e in m && f in m && e != f && m[e].1 != m[f].1 ==> (f !in freqMap[m[e].1]))) &&
      ((|m| > 0 && |freqMap| > 0) ==> (forall e, f :: e in m && f in freqMap && m[e].1 != f ==> (e !in freqMap[f]))) &&
      // if e's freq is unique, then in freqMap[freq], there should be only 1 element that is e
      ((|m| > 0 && |freqMap| > 0) ==> (
        (forall e, f :: e in m && f in m && e != f && |freqMap[m[e].1]| == 1 ==> (f !in freqMap[m[e].1])) 
      )) &&
      // (forall a, b :: a in m && b in m ==> a !=b) &&
      ((|this.m| > 0 && |this.freqMap| > 0) ==> this.minFreq in this.freqMap && |this.freqMap[this.minFreq]| > 0)
    } 
    
    //Remove element by a given value
    method Remove(oldSet: set<int>, element: int) returns (newSet: set<int>)
      requires |oldSet| > 0
      requires element in oldSet
      ensures |oldSet| - |newSet| == 1
      ensures element !in newSet
      ensures forall e :: e in newSet ==> e in oldSet;
      ensures forall e :: e in oldSet && e != element ==> e in newSet;
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
      requires |this.freqMap| > 0 ==> forall e :: e in m ==> m[e].1 in freqMap;
      requires |this.freqMap| > 0 ==> forall e :: e in this.freqMap ==> |this.freqMap[e]| > 0;
      requires |this.freqMap| > 0 ==> exists e :: e in this.freqMap && key in this.freqMap[e];
      requires |this.freqMap| > 0 ==> key in this.m && key in this.freqMap[this.m[key].1];
      requires |this.freqMap| > 0 ==> key in this.m && (this.m[key].1 + 1 !in this.freqMap || key !in this.freqMap[this.m[key].1 + 1]);
      modifies this;
      ensures Valid();
      ensures key !in m ==> value == -1;
      ensures key in old(m) ==> (key in m && value == m[key].0 && old(m[key].1) == (m[key].1 - 1)); // freq should increment
      ensures key in old(m) ==> (old(m[key]).1 !in freqMap) || (old(m[key]).1 in freqMap && key !in freqMap[old(m[key]).1]); // The freq should not in freqMap, or freqMap[freq] list should no longer contain the key
      ensures forall oldKey :: oldKey in old(m) ==> oldKey in m && old(m[oldKey].0) == m[oldKey].0; // The cache key and value does not change.
      // DO NOT need to check freqMap[freq+1] constains the key, as it is ensured by "ensures Valid(); && ensures key in m;" above.
    {
      // assert (|m| > 0 && |freqMap| > 0) ==> forall e :: e in m ==> (m[e].1 in freqMap && e in freqMap[m[e].1]);
      // assert (|m| > 0 && |freqMap| > 0) ==> (forall e, f :: e in m && f in m && e != f && m[e].1 != m[f].1 ==> (f !in freqMap[m[e].1]));
      if(key !in m){
        value := -1;
      }
      else{
        //update map with new freq
        assert (forall e, f :: e in m && f in m && e != f && |freqMap[m[e].1]| == 1 ==> (f !in freqMap[m[e].1]));
        // assert forall e, f :: e in this.m && f in this.m && e != f && this.m[e].1 == this.m[f].1 ==> (f in this.freqMap[this.m[e].1]);
        // assert forall e :: e in m ==> (m[e].1 in freqMap && e in freqMap[m[e].1]);
        // assert forall e :: (e in this.m  && e != key) ==> (this.m[e].1 in this.freqMap); // others are not affected
        value := m[key].0;
        var oldFreq := m[key].1;
        // assert key in this.freqMap[oldFreq];
        var newFreq := oldFreq + 1;
        // assert (old(this.m[key].1) == this.m[key].1);
        this.m := this.m[key := (value, newFreq)];
        // assert (oldFreq == m[key].1 - 1);
        // assert this.m[key].1 == newFreq;
        // assert old(this.m[key].1) == newFreq - 1;
        // assert old(this.m[key].1) == oldFreq;
        // assert old(this.m[key].1) == (this.m[key].1 - 1);
        // assert forall e :: (e in this.m && e != key) ==> (this.m[e].1 in this.freqMap);
        // assert forall e :: (e in this.m && e != key && this.m[e].1 == this.m[key].1) ==> e in this.freqMap[this.m[key].1];
        // assert forall e :: (e in this.m && e != key && this.m[e].1 != old(this.m[key].1)) ==> e !in this.freqMap[old(this.m[key].1)]; // need to use old here, as we changed this.m[key].1 above.

        // assert forall e :: e in this.m && e != key ==> (e in this.freqMap[this.m[e].1]);

        //remove from old frequency list
        var oldFreqList := this.freqMap[oldFreq];
        if |oldFreqList| == 1 {
          assert key in oldFreqList;
          // assert forall e :: (e in this.m && e != key && this.m[e].1 == this.m[key].1) ==> e in this.freqMap[this.m[key].1];
          // assert forall e :: (e in this.m && e != key && this.m[e].1 != old(this.m[key].1)) ==> e !in this.freqMap[old(this.m[key].1)]; // Need to use old()
          // assert forall e :: (e in this.m && e != key) ==> (this.m[e].1 in this.freqMap);
          // assert oldFreqList == this.freqMap[old(this.m[key].1)];
          // assert oldFreq == old(this.m[key].1);
          // assert key in oldFreqList;
          // assert forall e :: (e in this.m && e != key) ==> (e !in oldFreqList); 
          // assert oldFreq in this.freqMap;
          // assert key in this.freqMap[oldFreq];
          // assert old(this.m[key].1) in this.freqMap;
          // assert |this.freqMap[old(this.m[key].1)]| == 1;
          // assert forall e :: (e in this.m  && e != key) ==> this.m[e].1 != oldFreq;
          this.freqMap := this.freqMap - {oldFreq};
          // assert oldFreq !in this.freqMap;
          // assert forall e :: (e in this.m  && e != key) ==> (this.m[e].1 in this.freqMap);
          // assert forall e :: e in this.m && e != key ==> (e in this.freqMap[this.m[e].1]);
        } else {
          // assert forall e :: (e in this.m  && e != key) ==> (this.m[e].1 in this.freqMap);
          // assert oldFreq in this.freqMap;
          // assert key in oldFreqList;
          var removeList := Remove(oldFreqList, key);
          // assert key !in removeList;
          // assert forall e :: e in removeList ==> e in oldFreqList;
          // assert forall e :: e in oldFreqList && e != key ==> e in removeList;
          this.freqMap := this.freqMap[oldFreq := removeList];
          // assert forall e :: e in this.m && e != key ==> (e in this.freqMap[this.m[e].1]);
          // assert key !in this.freqMap[oldFreq];
        }
        // assert forall e :: (e in this.m  && e != key) ==> (this.m[e].1 in this.freqMap);
        
        // assert forall e :: e in this.m && e != key ==> (this.m[e].1 == old(this.m[e].1));
        // assert forall e :: e in this.m && e != key ==> (e in this.freqMap[this.m[e].1]);
        //add to new frequency list
        if (newFreq in this.freqMap) {
          var newFreqList := this.freqMap[newFreq];
          // assert key !in this.freqMap[newFreq];
          var addList := AddElement(newFreqList, key);
          this.freqMap := this.freqMap[newFreq := addList];
        } else {
          var newFreqList := {key};
          this.freqMap := this.freqMap[newFreq := newFreqList];
          
        }
        // assert key in this.freqMap[newFreq];
        // assert this.m[key].1 in this.freqMap;
        // assert forall e :: e in this.m ==> (this.m[e].1 in this.freqMap);
        // assert forall e, f :: e in this.m && f in this.m && e != f && this.m[e].1 == this.m[f].1 ==> (f in this.freqMap[this.m[e].1]);
        // assert forall e, f :: e in this.m && f in this.m && e != f && this.m[e].1 != this.m[f].1 ==> (f !in this.freqMap[this.m[e].1]);

        //update minFreq
        if(oldFreq == this.minFreq && oldFreq !in freqMap){
          minFreq := minFreq + 1;
        }

        // assert forall e :: e in this.m ==> (this.m[e].1 in this.freqMap);
        // assert forall e :: e in this.m ==> (this.m[e].1 in this.freqMap && e in this.freqMap[m[e].1]);
        assert (forall e, f :: e in m && f in m && e != f ==> (|freqMap[m[e].1]| == 1 ==> (f !in freqMap[m[e].1])));
      }
      // assert forall e :: (e in this.m && e != key && this.m[e].1 != this.m[key].1) ==> e !in this.freqMap[this.m[key].1];
      return value;
    }
    
    
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