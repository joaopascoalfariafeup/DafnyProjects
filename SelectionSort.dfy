/* 
* Formal verification of the selection sort algorithm with Dafny.
* FEUP, MIEIC, MFES, 2020/21.
*/

// Checks if array 'a' is sorted between positions 'from' (inclusive) and 'to' (exclusive).
ghost predicate isSorted(a: array<real>, from: nat, to: nat)
  requires 0 <= from <= to <= a.Length
  reads a
{
    forall i, j :: from <= i < j < to ==> a[i] <= a[j] 
}

// Sorts array 'a' using the selection sort algorithm.
method selectionSort(a: array<real>)
  modifies a
  ensures isSorted(a, 0, a.Length) 
  ensures multiset(a[..]) == multiset(old(a[..]))
{
    for i := 0 to a.Length 
      invariant isSorted(a, 0, i)
      invariant forall lhs, rhs :: 0 <= lhs < i <= rhs < a.Length ==> a[lhs] <= a[rhs] 
      invariant multiset(a[..]) == multiset(old(a[..]))
    {
        var j := findMin(a, i, a.Length);
        a[i], a[j] := a[j], a[i];
    }
}

// Finds the position of a miminum value in non-empty subarray 'a' between positions 
// 'begin' (inclusive) and 'end' (exclusive)
method findMin(a: array<real>, begin: nat, end: nat) returns(index: nat)
  requires 0 <= begin < end <= a.Length
  ensures begin  <= index < end
  ensures forall k :: begin <= k < end ==> a[k] >= a[index]
{
    index := begin; // position of min up to position i (excluded)
    for i := begin + 1 to end
      invariant begin <= index < i <= end
      invariant forall k :: begin <= k < i ==> a[k] >= a[index]  
    {
        if a[i] < a[index] {
            index := i;
        }
    }
}

method testSelectionSort() {
  var a := new real[5] [9.0, 4.0, 6.0, 3.0, 8.0];
  assert a[..] == [9.0, 4.0, 6.0, 3.0, 8.0]; // to help Dafny ...
  selectionSort(a);
  assert a[..] == [3.0, 4.0, 6.0, 8.0, 9.0];
}

method testFindMin() {
  var a := new real[5] [9.0, 5.0, 6.0, 4.0, 8.0];
  var m := findMin(a, 0, 5);
  assert a[3] == 4.0; // to help Dafny ... 
  assert m == 3;
}
