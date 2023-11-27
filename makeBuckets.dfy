type T = nat 

// Given a non-empty array 'a' of natural numbers, generates a new array ‘b’ 
// (buckets) such that b[k] gives the number of occurrences of 'k' in 'a',
// for 0 <= k <= m, where 'm' denotes the maximum value in 'a'.
method makeBuckets(a: array<nat>) returns(b: array<nat>)
  requires a.Length > 0
  ensures fresh(b) 
  ensures b.Length  == max(a[..]) + 1
  ensures forall k :: 0 <= k < b.Length ==> b[k] == count(k, a[..])
{
   var max := max(a[..]);
   b := new T[1 + max];
   forall k | 0 <= k <= max {
     b[k] := 0;
   }
   assert a[..] == old(a[..]); // proof helper
   for i := 0 to a.Length
    invariant forall k :: 0 <= k < b.Length ==> b[k] == count(k, a[..i])
   {
      b[a[i]] := b[a[i]] + 1; 
   } 
   assert a[..] == a[..a.Length]; // proof helper
}

// Finds the maximum value in a non-empty sequence.
function max(s: seq<T>) : T
  requires |s| > 0 
  ensures isMax(max(s), s)
{
  if |s| == 1 then s[0]
  else (var m := max(s[1..]); if m > s[0] then m else s[0])
}

// Checks if 'x' is a maximum in sequence 's'
predicate isMax(x: T, s: seq<T>) {
  (exists k :: 0 <= k < |s| && x == s[k])
  && (forall k :: 0 <= k < |s| ==> x >= s[k])
}

// Counts the number of occurrences of 'x' in sequence 's'
function count(x: T, s: seq<T>) : nat {
   multiset(s)[x]
}

// A simple test case (checked statically)
method testMakeBuckets() {
    var a1 := new nat[] [1, 1, 3, 3, 3, 5];
    assert a1[..] == [1, 1, 3, 3, 3, 5];
    var b1 := makeBuckets(a1);
    assert b1[..] == [0, 2, 0, 3, 0, 1]; 
    var a2 := new nat[] [0];
    assert a2[..] == [0];
    var b2 := makeBuckets(a2);
    assert b2[..] == [1];
}
