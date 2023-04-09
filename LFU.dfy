class LFUCache {

    var capacity : int;
    var minFreq : int;
    var m : map<int, (int, int)>; //key -> {value, freq}
    var freqMap: map<int, set<int>>; //freq -> list of keys

     constructor(capacity: int)
        requires capacity >= 0;
        ensures Valid();
    {
      this.capacity := capacity;
      this.minFreq := 0;
    }

    predicate Valid()
      reads this;
    {
      // general value check
      this.capacity >= 0 && this.minFreq >= 0 && 
      // either both map are empty or both are not
      (|m| == |this.freqMap| == 0 || (|m| > 0 && |freqMap| > 0)) && 
      // for all keys in m, its freq must be in freqMap, and the freqMap[freq] array must contain key
      //TODO: when accessing the element in set, need to convert to multiset first
      (|m| > 0 && |freqMap| > 0) ==> forall e :: e in m && m[e].1 in freqMap && (exists i :: 0 <= i < |this.freqMap[m[e].1]| && freqMap[m[e].1][i] == e) 
    } 
    
    //Remove element by a given value
    method Remove(oldSet: set<int>, element: int) returns (newSet: set<int>)
      requires |oldSet| > 0
      requires element in oldSet
      ensures |oldSet| - |newSet| == 1
      ensures element !in newSet
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
    {
      var elementSet := {element};
      newSet := oldSet + elementSet;
      return newSet;
    }

    method get(key: int) returns (value: int){
      if(key in m){
        value := -1;
      }
      else{
        //update map with new freq
        value := m[key].0;
        var oldFreq := m[key].1;
        var newFreq := oldFreq + 1;
        m := m[key := (value, newFreq)];
        
        //remove from old frequency list
        var oldFreqList := freqMap[oldFreq];
        var removeList := Remove(oldFreqList, key);
        freqMap := freqMap[oldFreq := removeList];
        
        //TODO: check if the new frequency exists. If not, create one
        //add to new frequency list
        var newFreqList := freqMap[newFreq];
        var addList := AddElement(newFreqList, key);
        freqMap := freqMap[newFreq := addList];
      }
      
      //update minFreq
      var minFreqList := freqMap[minFreq];
      if(|minFreqList| == 0){
        minFreq := minFreq + 1;
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
   
