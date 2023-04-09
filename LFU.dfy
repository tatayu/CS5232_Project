class LFUCache {

    var capacity : int;
    var minFreq : int;
    var m : map<int, (int, int)>; //key -> {value, freq}
    var freqMap: map<int, array<int>>; //freq -> list of keys

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
      (|m| > 0 && |freqMap| > 0) ==> forall e :: e in m && m[e].1 in freqMap && (exists i :: 0 <= i < this.freqMap[m[e].1].Length && freqMap[m[e].1][i] == e) 
    } 
    
    //Remove element by a given value
    method RemoveByValue(a: array<int>, element: int) returns (newArray: array<int>)
    {
      newArray := new int[a.Length - 1];
      var i := 0;
      var j := 0;
      while i < a.Length
      {
        if(a[i] != element){
          newArray[j] := a[i];
          i := i + 1;
          j := j + 1;
        }
      }
      return newArray;
    }

    //Remove element by a given index
    method RemoveByIndex(a: array<int>, index: int) returns (newArray: array<int>, element: int)
    {
      newArray := new int[a.Length - 1];
      var i := 0;
      var j := 0;
      while i < a.Length
      {
        if(i != index){
          newArray[j] := a[i];
          i := i + 1;
          j := j + 1;
        }else{
          element := a[i];
        }
      }
      return newArray, element;
    }

    //Add element to the last of the array
    method AddElement(a: array<int>, element: int) returns (newArray: array<int>)
    {
      newArray := new int[a.Length + 1];
      var i := 0;
      while i < a.Length
      {
        newArray[i] := a[i];
        i := i + 1;
      }
      newArray[i] := element;

      return newArray;
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
        var oldFreqList := freq[oldFreq];
        var removeList := RemoveByValue(oldFreqList, key);
        freq := freq[oldFreq := removeList];
        
        //add to new frequency list
        var newFreqList := freq[newFreq];
        var addList := AddElement(newFreqList, key);
        freq := freq[newFreq := addList];
      }
      
      //update minFreq
      var minFreqList := freq[minFreq];
      if(minFreqList.Length == 0){
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
          var oldLFUList := freq[minFreq];
          
          //update freq by removing the LFU element
          var newLFUList, LFUElement := RemoveByIndex(oldLFUList, 0);
          freq := freq[minFreq := newLFUList];

          //update map by removing the LFU element
          m := m - {LFUElement};
        }

        //update map by putting the new element
        var new_m : map<int, (int, int)>;
        new_m := new_m[key := (value, 1)];
        m := m + new_m;

        //update freq
        var LFUListOne := freq[1];
        var newLFUListOne := AddElement(LFUListOne, key);
        freq := freq[1 := newLFUListOne];

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
   
