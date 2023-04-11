class LFUCache {

    var capacity : int;
    var cacheMap : map<int, (int, int)>; //key -> {value, freq}

    constructor(capacity: int)
      requires capacity > 0;
      ensures Valid();
    {
      this.capacity := capacity;
      this.cacheMap := map[];
    }

    predicate Valid()
      reads this;
      // reads this.freqMap.Values;
    {
      // general value check
      this.capacity > 0 &&
      0 <= |cacheMap| <= capacity &&
      (|cacheMap| > 0 ==> (forall e :: e in cacheMap ==> cacheMap[e].1 >= 1)) && // frequency should always larger than 0
      (|cacheMap| > 0 ==> (forall e :: e in cacheMap ==> cacheMap[e].0 >= 0)) // only allow positive values
    } 

    method getLFUKey() returns (lfuKey : int) 
      requires Valid();
      requires |cacheMap| > 0;
      ensures Valid();
      ensures lfuKey in cacheMap;
      ensures forall k :: k in cacheMap.Items ==> cacheMap[lfuKey].1 <= cacheMap[k.0].1;
    {
      

      var items := cacheMap.Items;
      var seenItems := {};

      var anyItem :| anyItem in items;
      var minFreq := anyItem.1.1;
      lfuKey := anyItem.0;

      while items != {}
        decreases |items|;
        invariant cacheMap.Items >= items;
        invariant cacheMap.Items >= seenItems;
        invariant cacheMap.Items == seenItems + items;
        invariant lfuKey in cacheMap;
        invariant cacheMap[lfuKey].1 == minFreq;
        invariant forall e :: e in seenItems ==> minFreq <= e.1.1;
        invariant forall e :: e in seenItems ==> minFreq <= cacheMap[e.0].1;
        invariant forall e :: e in seenItems ==> cacheMap[lfuKey].1 <= cacheMap[e.0].1;
        invariant exists e :: e in seenItems + items ==> minFreq == e.1.1;
      {
        var item :| item in items;

        if (item.1.1 < minFreq) {
          lfuKey := item.0;
          minFreq := item.1.1;
        }
        items := items - { item };
        seenItems := seenItems + { item };
      }
      assert seenItems == cacheMap.Items;
      assert cacheMap[lfuKey].1 == minFreq;
      assert forall e :: e in seenItems ==> minFreq <= e.1.1;
      assert forall e :: e in cacheMap.Items ==> minFreq <= e.1.1;
      assert forall k :: k in seenItems ==> cacheMap[lfuKey].1 <= cacheMap[k.0].1;
      assert forall k :: k in cacheMap.Items ==> cacheMap[lfuKey].1 <= cacheMap[k.0].1;
      return lfuKey;
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
      modifies this;
      ensures Valid();
      ensures key !in cacheMap ==> value == -1;
      ensures forall e :: e in old(cacheMap) <==> e in cacheMap;
      ensures forall e :: e in old(cacheMap) ==> (old(cacheMap[e].0) == cacheMap[e].0);
      ensures key in cacheMap ==> value == cacheMap[key].0 && old(cacheMap[key].1) == cacheMap[key].1-1;
    {
      assert key in cacheMap ==> cacheMap[key].0 >= 0;
      if(key !in cacheMap) {
        value := -1;
      }
      else{
        assert key in cacheMap;
        assert cacheMap[key].0 >= 0;
        value := cacheMap[key].0;
        var oldFreq := cacheMap[key].1;
        var newV := (value, oldFreq + 1);
        cacheMap := cacheMap[key := newV];
      }
      return value;
    }
    
    
     method put(key: int, value: int)
        requires Valid();
        requires value > 0;
        modifies this
        ensures Valid();
       
     {
        if (key in cacheMap) {
          var currFreq := cacheMap[key].1;
          cacheMap := cacheMap[key := (value, currFreq)];
        } else {
          if (|cacheMap| < capacity) {
            cacheMap := cacheMap[key := (value, 1)];
          } else {
            var LFUKey := getLFUKey();
            assert LFUKey in cacheMap;
            assert |cacheMap| == capacity;
            ghost var oldMap := cacheMap;
            var newMap := cacheMap - {LFUKey};
            cacheMap := newMap;
            assert newMap == cacheMap - {LFUKey};
            assert LFUKey !in cacheMap;
            assert LFUKey in oldMap;
            assert |cacheMap| < |oldMap|; // ????
            cacheMap := cacheMap[key := (value, 1)];
          }
        }
       
     }
 }

 method Main()
 {
  //  var LFUCache := new LFUCache(2);
  //  LFUCache.put(1,1);
  //  assert((|LFUCache.m| == 0 <==> |LFUCache.freqMap| == 0) || (|LFUCache.m| > 0 <==> |LFUCache.freqMap| > 0));
  //  LFUCache.put(2,2);
  //  var val := LFUCache.get(1);
  //  print val;
  //  LFUCache.put(3,3);
 }