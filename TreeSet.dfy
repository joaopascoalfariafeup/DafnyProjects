/* 
* Specification and verification of a sorted set implemented with a binary search tree (BST).
* Illustrates the usage of ghost variables for data abstraction and separation of specification and implementation.
* Uses the {:autocontracts} attribute to take care of class invariant enforcement and frame generation (read/modifies).
* Possible improvements: improve deletion; create wrapper class TreeSet.
* João Pascoal Faria (jpf@fe.up.pt), FEUP, Jan/2022.
*/

type T = int // for demo purposes 

// Sequence without duplicates
type  useq<T> =  s: seq<T> | !hasDuplicates(s)

// Checks if a sequence 's' has duplicates.
predicate hasDuplicates<T>(s: seq<T>)  {
    exists i, j :: 0 <= i < j < |s| && s[i] == s[j]
}

// Node of a binary search tree
class {:autocontracts} BSTNode {
    // Concrete implementation variables
    var value: T // value in this node
    var left: BSTNode?  // elements smaller than 'value' (? - may be null)
    var right: BSTNode? // elements greater than 'value' (? - may be null)
    
    // Abstract variable used for specification & verification purposes
    ghost var elems: set<T> // set of values in the subtree starting in this node (including this value)

    // Class invariant with the integrity constraints for the above variables
    predicate Valid() {  
        (elems == {value} + (if left == null then {} else left.elems)
                          + (if right== null then {} else right.elems))
        && (left != null ==> forall x :: x in left.elems ==> x < value)
        && (right != null ==> forall x :: x in right.elems ==> x > value)
        && (right != null ==> forall x :: x in right.elems ==> x > value)
        && (left != null ==> left.Valid())         
        && (right != null ==> right.Valid())
        && (left != null && right != null ==> left.Repr !! right.Repr) 
           // disjoints sets of objects in left and right subtree,
           // needed to make sure that changing nodes in one subtree doesn't affect the other!    
    }

    // Initializes a new node with value 'x' and empty left and right subtrees.
    constructor (x: T)
      ensures elems == {x}
    {
        value := x;
        left := null;
        right := null;
        elems := {x};
    } 

    // Checks if the subtree starting in this node contains a value 'x'
    // Runs in time O(log h), where 'h' is the height of the subtree.
    predicate method contains(x: T) 
      ensures contains(x) <==> x in elems
    {
        if x == value then true
        else if x < value && left != null then left.contains(x)
        else if x > value && right != null then right.contains(x)
        else false
    }

    // Inserts a value 'x' in the subtree starting in this node.
    // If the value already exists, does nothing.
    // Runs in time O(log h), where 'h' is the height of the subtree.
    method insert(x: T)
      ensures elems == old(elems) + {x}
      decreases elems
    {
        if  x == value {
            return;
        } 
        else if x < value {
            if left == null {
                left := new BSTNode(x);
            }
            else {
                left.insert(x);
            }
        }
        else {
            if right == null {
                right := new BSTNode(x);
            }
            else {
                right.insert(x);
            }
        }
        elems := elems + {x};
    }

    // Public function to find the maximum value in this subtree.
    // Runs in time O(log h), where 'h' is the height of the subtree.
    function method max() : T
      ensures max() in elems && forall x :: x in elems ==> x <= max()
    {
        if right == null then value else right.max()
    }

    // Public function to find the minimum value in this subtree.
    // Runs in time O(log h), where 'h' is the height of the subtree.
    function method min() : T
      ensures min() in elems && forall x :: x in elems ==> x >= min()
    {
        if left  == null then value else left.min()
    }

    // Deletes a value 'x' from the subtree starting in this node, and returns the new head 
    // of the subtree (which will be null if 'x' was the only value in the subtree).
    // If the value doesn't exist, does nothing.
    // Currently, seems to run in time O(log h * log h), where 'h' is the height of the subtree.
    method delete(x: T) returns(res: BSTNode?)
      ensures if old(elems) == {x} then res == null 
              else res != null && res.elems == old(elems) - {x} 
                   && res.Valid() // not added automatically by autocontracts ...
                   && res.Repr <= old(Repr) // to preserve disjointness ...
      decreases elems
    {
        if  x == value {
           if left == null {
                res := right; // just changes the head
                return;
            }
            else if right == null {
                res := left; // just changes the head
                return;
            }
            else {
                if * /* non deterministic choice */ { 
                    value := left.max();
                    left := left.delete(value);
                }
                else {
                    value := right.min();
                    right := right.delete(value);
                }
            }
        } 
        else if x > value && right != null {
            right := right.delete(x);
        }
        else if x < value && left != null {
            left := left.delete(x);
        }
        res := this;
        elems := elems - {x};
    }

    method asSeq() returns (s: useq<T>)
      ensures isSorted(s) && asSet(s) == elems
      decreases elems
    {
        var l, m, r := [], [value], [];
        if left != null { l := left.asSeq(); }
        if right != null { r := right.asSeq(); }
        asSetProp(l, m); // recall lemma
        asSetProp(l + m,  r); // recall lemma
        return l + m + r;
    }
}

// Auxiliary function that obtains the set of elements in a sequence.
function asSet(s: seq<T>) : set<T> 
  ensures forall i :: 0 <= i < |s| ==> s[i] in asSet(s)
  ensures forall x :: x in asSet(s) ==> x in s
{ 
    if |s| == 0 then {} else {s[0]} + asSet(s[1..])  
}

// Auxiliary predicate that checks if a sequence is strictly sorted.
predicate isSorted(s: useq<T>) {
    forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
}

// Lemma that states and proves by induction the following property: the set of elements 
// of sequence concatenation is the union of the individual sets of elements.
lemma asSetProp(s1: seq<T>, s2: seq<T>)
  ensures asSet(s1 + s2) == asSet(s1) + asSet(s2)
{
    if |s1| > 0 {
        assert s1 == s1[..1] + s1[1..];
        assert (s1[..1] + s1[1..]) + s2 == s1[..1] + (s1[1..] + s2);
        asSetProp(s1[1..], s2);
    } 
    else {
        assert [] + s2 == s2;
    }
}

// Lemma that states and proves by induction the following property: if two sequences without 
// duplicates are sorted and have the same set of elements, then they must be identical. 
lemma sortingUniqueness(a: useq<T>, b: useq<T>)
  requires isSorted(a) && isSorted(b) && asSet(a) == asSet(b)
  ensures a == b
{
    if |a| > 0 {
        sortingUniqueness(a[1..], b[1..]);
    }
}

// A simple test case.
method testSortedSet() {
    var s := new BSTNode(2);
    s.insert(5);
    s.insert(1);
    s.insert(4);
    s.insert(4);
    var t := s.asSeq();
    sortingUniqueness(t, [1, 2, 4, 5]); // to help prove next assertion
    assert t == [1, 2, 4, 5];
    assert s.min() == 1;
    assert s.max() == 5;
    var s2 := s.delete(5);
    assert s2.elems == {1, 2, 4};
}