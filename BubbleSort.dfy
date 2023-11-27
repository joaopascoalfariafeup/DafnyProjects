/* 
* Formal verification of the bubble sort algorithm with Dafny.
* The algorithm was taken from https://en.wikipedia.org/wiki/Bubble_sort .
* FEUP, MIEIC, MFES, 2020/21.
*/

type T = int // for demo purposes, but could be other type


// Checks if subarray a[from], ..., a[to-1] is sorted.
ghost predicate isSorted(a: array<T>, from: nat := 0, to: nat := a.Length)
  requires 0 <= from <= to <= a.Length
  reads a
{
  forall i, j :: from <= i < j < to ==> a[i] <= a[j]
}

// Checks if all elements in subarray a[i], ..., a[j-1] are less or equal than
// all elements in subarray a[k], ..., a[l-1].
ghost predicate leq(a: array<T>, i: nat, j: nat, k: nat, l: nat)
  requires 0 <= i <= j <= a.Length && 0 <= k <= l <= a.Length
  reads a
{
  forall x, y :: i <= x < j && k <= y < l ==> a[x] <= a[y]
}

// Sorts array 'a' using the bubble sort algorithm.
method bubbleSort(a: array<T>)
  modifies a
  ensures isSorted(a)
  ensures multiset(a[..]) == multiset(old(a[..]))
{
    var n := a.Length; 
    while n  > 1
      invariant 0 <= n <= a.Length
      invariant isSorted(a, n) && leq(a, 0, n, n, a.Length)
      invariant multiset(a[..]) == multiset(old(a[..]))
    {
      var newn : nat := 0;
      for i:= 1 to n
        invariant newn < i 
        invariant isSorted(a, n) && leq(a, 0, n, n, a.Length)
        invariant isSorted(a, newn, i) && leq(a, 0, newn, newn, i)
        invariant multiset(a[..]) == multiset(old(a[..]))
      {
          if (a[i-1] > a[i]) { 
              a[i-1], a[i] := a[i], a[i-1]; 
              newn := i;
          }
      }
      n := newn;
    }
}

// A simple test case (checked statically)
method testBubbleSort() {
    var a := new int[] [7, 4, 6, 3, 8, 9];
    assert a[..] == [7, 4, 6, 3, 8, 9];
    bubbleSort(a);
    assert isSorted(a);
    assert a[..] == [3, 4, 6, 7, 8, 9];
}
