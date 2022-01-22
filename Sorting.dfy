/* 
 * Formal verification of the insertion sort algorithm with Dafny. 
 * J. Pascoal Faria, FEUP, Jan/2022.
 */

 // Contract for sorting algorithms.
abstract module Sorting {
  type T = int // for demo purposes, but could be another type

  // Abstract method defining the contract (semantics) of array sorting.
  method sort(a: array<T>)
    modifies a    
    ensures isSorted(a[..])
    ensures multiset(a[..]) == multiset(old(a[..]))

  // Auxiliary predicate that checks if a sequence 'a' is sorted. 
  predicate isSorted(s: seq<T>) {
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j] 
  }
}

 // Static tests of the Sorting contract 
abstract module TestSorting {
  import opened Sorting  

  method testSortSimple() {
    var a := new T[] [9, 4, 6, 3, 8]; 
    assert a[..] == [9, 4, 6, 3, 8]; // prover helper!
    sort(a);
    assert a[..] == [3, 4, 6, 8, 9];
  }  

  method testSortWithDups() {
    var a := new T[] [9, 3, 6, 9];
    assert a[..] == [9, 3, 6, 9]; // prover helper
    sort(a);
    SortingUniquenessProp(a[..],  [3, 6, 9, 9]);
    assert a[..] ==  [3, 6, 9, 9]; // assertion violation (!?)
  }

  // State and prove by induction the property that, if two sequences are sorted and have 
  // the same multiset of elements, then they must be identical (so sorting has a unique solution). 
  lemma SortingUniquenessProp(a: seq<T>, b: seq<T>)
    requires isSorted(a) && isSorted(b) && multiset(a) == multiset(b) 
    ensures a == b
  {
    // recalls useful properties about sequences and their multisets  
    seqProps(a);
    seqProps(b);

    // key steps of proof by induction on 'a' and 'b' (the rest is filled in by Dafny) 
    if |a| > 0 {
      SortingUniquenessProp(a[1..], b[1..]);
    }
  }

  // States two properties about sequences (proved by Dafny alone): 
  // - sequence concatenation reverts splitting in head and tail;
  // - elements of a sequence belong to its multiset.
  lemma seqProps(a: seq<T>) 
    ensures |a| > 0 ==> a == [a[0]] + a[1..] 
    ensures forall i :: 0 <= i < |a| ==> a[i] in multiset(a)
  {}
}


module InsertionSort refines Sorting {

  // Sorts array 'a' using the insertion sort algorithm.
  // Inherits the contract from Sorting.
  method sort(a: array<T>) {
    for i := 0 to a.Length
      invariant isSorted(a[..i]) 
      invariant multiset(a[..]) == multiset(old(a[..]))
    {
      var j := i;
      while j > 0 && a[j-1] > a[j]
        invariant forall l, r :: 0 <= l < r <= i && r != j ==> a[l] <= a[r] 
        invariant multiset(a[..]) == multiset(old(a[..]))
      {
        a[j-1], a[j] := a[j], a[j-1]; // swap (parallel assignment)
        j := j - 1;
      }
    }
  }

}

