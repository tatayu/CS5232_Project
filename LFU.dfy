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
      requires a.Length > 0;
    {
      newArray := new int[a.Length - 1];
      var i := 0;
      var j := 0;
      while i < a.Length
       decreases a.Length - i;
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
      requires a.Length > 0;
      requires index < a.Length;
      ensures exists i :: 0 <= i < a.Length && a[i] == element; // Element belonged to a
      ensures newArray.Length == a.Length + 1; // new_array has correct size
      ensures forall i :: (exists j :: 0 <= i < newArray.Length && 0 <= j < a.Length && newArray[i] == a[j]); // all elements in new_array are in a
      ensures forall i :: 0 <= i < newArray.Length && newArray[i] != element; // the removed element not in new_array
    {
      newArray := new int[a.Length - 1];
      
      var i := 0;
      var j := 0;
      while i < a.Length
        decreases a.Length - i;
        invariant i < index ==> i == j;
        invariant i >= index ==> (i == j + 1 || i == j == 0);
        invariant j < newArray.Length;
      {
        if(i != index){
          assert newArray.Length == a.Length-1;
          newArray[j] := a[i];
          j := j + 1;
        }else{
          element := a[i];
        }
        i := i + 1;
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

    method get(key: int) returns (value: int)
      requires Valid();
      modifies this;
      ensures Valid();
      ensures key !in m ==> value == -1;
      ensures key in old(m) ==> (key in m && value == m[key].0 && old(m[key]).1 == m[key].1 + 1);
    {
      if(key !in m){
        value := -1;
      }
      else{
        //update map with new freq
        value := m[key].0;
        var oldFreq := m[key].1;
        var newFreq := oldFreq + 1;
        m := m[key := (value, newFreq)];
        
        //remove from old frequency list
        var oldFreqList := this.freqMap[oldFreq];
        var removeList := RemoveByValue(oldFreqList, key);
        this.freqMap := this.freqMap[oldFreq := removeList];
        
        //add to new frequency list
        var newFreqList := this.freqMap[newFreq];
        var addList := AddElement(newFreqList, key);
        this.freqMap := this.freqMap[newFreq := addList];
      }
      
      //update minFreq
      var minFreqList := this.freqMap[minFreq];
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