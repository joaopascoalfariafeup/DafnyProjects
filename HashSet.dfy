/*
 * Verified implementation of a hash set with open addressing and linear probing in Dafny.
 * Provides the fundamental set operations (contains, insert, delete), specified at an abstract level,
 * resorting to an abstract state variables 'elems' with the set contents. 
 * João Pascoal Faria (jpf@fe.up.pt), FEUP, Janeiro/2022.
 */

// Datatype for the content of each cell of the hash table.
// It stores a value of type T, Nil (no value) or Deleted (cell marked as deleted).
datatype Cell<T> = Nil | Deleted | Some(value: T) 

// Function type for hash functions 
type HashFunction<!T> = (T) -> nat 

// Represents a hash set of elements of type T (comparable for equality), i.e., a set stored in a hash table. 
// Uses the "autocontracts" attribute to automatically inject class invariant checking and frame conditions
// in methods' pre and post-conditions.
class {:autocontracts} HashSet<T(==)> {

  // Ghost variable (abstract state variable) used for specification purposes only.
  ghost var elems : set<T>;

  // Concrete state variable with internal representation (array). 
  var hashTable: array<Cell<T>>; 

  // Hash function to be used (provided to the constructor). 
  const hash: HashFunction<T>;

  // Number of positions used (with some value) and marked as deleted in the hash table. 
  var used: nat;
  var deleted: nat;

  // Initial capacity of the hash table.
  static const initialCapacity := 101;

  // Ghost predicate that formalizes the class invariant.
  predicate Valid()  {
    // Constraint that define the abstraction relation between abstract and concrete state variables
    elems == valSet(hashTable, hashTable.Length) 
    // Constraints on the internal state representation
    && hashTable.Length > 0 
    && hashTableInv(hashTable)
    && used == |valSet(hashTable, hashTable.Length)|
    && deleted == |delSet(hashTable, hashTable.Length)|
  }

  // Ghost predicate that checks the consistency of a hash table 't'. 
  predicate {:autocontracts false} hashTableInv(t: array<Cell<T>>)
    reads t 
  { 
    forall i :: 0 <= i < t.Length && t[i].Some? ==> validPos(t[i].value, i, t)
  }

  // Ghost predicate that checks that 'i' is a valid position for value 'x' in hash table 't'.
  // ('x' may be or not currently stored in that position) 
  predicate {:autocontracts false} validPos(x: T, i: nat, t: array<Cell<T>>)
    requires 0 <= i < t.Length
    reads t 
  {
    var h := hash(x) % t.Length;
    h == i  
    || (h < i && forall j :: h <= j < i ==> t[j] != Nil && t[j] != Some(x))
    || (h > i && forall j :: h <= j < t.Length || 0 <= j < i ==> t[j] != Nil && t[j] != Some(x))
  }

  // Ghost function that retrieves the set of values stored in the first 'n' positions of hash table 't'. 
  function {:autocontracts false} valSet(t: array<Cell<T>>, n: nat): set<T>
    requires 0 <= n <= t.Length
    reads t
  { set i | 0 <= i < n && t[i].Some? :: t[i].value }

  // Ghost function that retrieves the set of positions marked as Deleted in the first 'n' positions of hash table 't'. 
  function {:autocontracts false} delSet(t: array<Cell<T>>, n: nat): set<nat> 
    requires 0 <= n <= t.Length
    reads t
  { set i | 0 <= i < n && t[i].Deleted? }

  // Ghost function that retrieves the set of positions marked as Nil in the first 'n' positions of hash table 't'. 
  function {:autocontracts false} nilSet(t: array<Cell<T>>, n: nat): set<nat> 
    requires 0 <= n <= t.Length
    reads t
  { set i | 0 <= i < n && t[i].Nil? }

  // Auxiliary lemma that states the following property: the sum of the sizes of valSet, delSet and nilSet
  // of a valid hash table is equal to the length of the hash table (array). 
  // This is true because the hash table invariant implies that there are no duplicate values stored. 
  // The proof is done by induction on the length of the table (omitting steps filled in by Dafny).
  lemma {:autocontracts false} countingLemma(ht: array<Cell<T>>, len: nat, v: nat, d: nat, n: nat)
    requires 0 <= len <= ht.Length
    requires hashTableInv(ht)
    requires v == |valSet(ht, len)| && d == |delSet(ht, len)| && n == |nilSet(ht, len)|
    ensures v + d + n == len
  {
     if len > 0 {
        var vs, ds, ns := valSet(ht, len), delSet(ht, len), nilSet(ht, len); 
        var vs1, ds1, ns1 := valSet(ht, len-1), delSet(ht, len-1), nilSet(ht, len-1); 
        // recursive part
        countingLemma(ht, len-1, |vs1|, |ds1|, |ns1|);
        // incremental part
        match ht[len-1] {
          case Deleted => assert vs == vs1 && ds == ds1 + {len-1} && ns == ns1;
          case Nil     => assert vs == vs1 && ds == ds1 && ns == ns1 + {len-1};
          case Some(x) => assert vs == vs1 + {x} && ds == ds1 && ns == ns1;
        }
     }
  }

  // Internal predicate that checks if the hash table is 'full', in the sense
  // that all positions are occupied with a value or are marked as deleted (i.e., 
  // there are no positions with Nil).
  // In that case, inserting a new value might not be possible. 
  predicate method full()
    ensures full() <==> nilSet(hashTable, hashTable.Length) == {} 
  {
    // to help proving the post-condition (equivalence):  
    countingLemma(hashTable, hashTable.Length, used, deleted, |nilSet(hashTable, hashTable.Length)|);
    // the actual function value
    used + deleted == hashTable.Length
  } 
  
  // Public method that checks if this set contains a value 'x'.
  method contains(x: T) returns (res: bool)
    ensures res <==> x in elems
  {
    var pos := locate(x);
    return pos != -1 && hashTable[pos] == Some(x);
  }

  // Internal method that determines the location ('pos') for a value 'x' (existent or to be inserted).
  // If such a location cannot be found (because the table is full), returns -1.
  // In the case of a new value, tries to reuse positions marked as deleted.
  method locate(x: T) returns (pos: int)
    requires Valid()
    ensures x in elems ==> 0 <= pos < hashTable.Length && hashTable[pos] == Some(x)
    ensures x !in elems ==> (pos == -1 && full()) || 
                            (0 <= pos < hashTable.Length && !hashTable[pos].Some? && validPos(x, pos, hashTable))
  {
     var h := hash(x) % hashTable.Length;
     var reuse := -1;
     for i := h to hashTable.Length 
       invariant forall j :: h <= j < i ==> hashTable[j] != Nil && hashTable[j] != Some(x)
       invariant reuse == -1 || (h <= reuse < i && hashTable[reuse] == Deleted)  
     {
        if hashTable[i] == Nil || hashTable[i] == Some(x) {
          return i;
        }
        if hashTable[i] == Deleted && reuse == -1 {
           reuse := i;
        }
     }
     for i := 0 to h 
       invariant forall j :: 0 <= j < i || h <= j < hashTable.Length ==> hashTable[j] != Nil && hashTable[j] != Some(x)
       invariant reuse == -1 || ((0 <= reuse < i || h <= reuse < hashTable.Length) && hashTable[reuse] == Deleted)
     {
        if hashTable[i] == Nil || hashTable[i] == Some(x) {
          return i;
        }
        if hashTable[i] == Deleted && reuse == -1 {
           reuse := i;
        }
     }
     return reuse;
  }

  // Public constructor that receives the hash function to be used and initializes the set as empty.
  constructor (hash: HashFunction<T>)
    ensures elems == {}
  {
    // initialize concrete state variables 
    this.hash := hash;
    hashTable := new Cell<T>[initialCapacity] (_ => Nil);
    used := 0;
    deleted := 0;
    // initialize ghost/abstract state variables 
    elems := {};
  }

  // Internal method that inserts a new value 'x' into the hash set, guaranteed to be not full.
  method insertAux(x : T)
    requires x !in elems
    requires ! full()
    ensures elems == old(elems) + {x}
    ensures deleted <= old(deleted) // usefull for rehash?
    ensures hashTable == old(hashTable) // usefull for rehash?
 {
    var i := locate(x);
    if hashTable[i] == Deleted {
      // to help proving that deleted > 0
      assert i in delSet(hashTable, hashTable.Length);

      // now, can decrement
      deleted := deleted - 1;
    } 
    hashTable[i] := Some(x);
    used := used + 1;
    elems := elems + {x};

    // to help proving that elems == valSet()  
    assert forall k :: 0 <= k < hashTable.Length && k != i ==> hashTable[k] == old(hashTable[k]);
    
    // to help proving that deleted == |delSet()|
    assert delSet(hashTable, hashTable.Length) == old(delSet(hashTable, hashTable.Length)) - {i};
  }

  // Internal method that grows and cleans up the hash table.
  method rehash()
   ensures ! full()
   ensures elems == old(elems)
  {
    var oldTable := hashTable;

    hashTable := new Cell<T>[hashTable.Length * 2 + 1] (_ => Nil); 
    deleted := 0;
    used := 0;
    elems := {};    
    // need also to update ghost variable 'Repr' generated by :autocontracts,
    // to be able to call InsertAux in a valid state
    Repr := {this, hashTable};

    for i := 0 to oldTable.Length
      invariant elems == valSet(oldTable, i)
      invariant deleted == 0 // to prove !full()
      invariant oldTable !in Repr // to assure is not changed by insertAux
      invariant Valid() // to ensure consistency is maintained
      invariant oldTable.Length < hashTable.Length // to prove !full()
      invariant fresh(Repr - old(Repr)) // to enable insertAux to modify the new hashTable
      invariant oldTable.Length < hashTable.Length // to prove !full()
      invariant forall k :: 0 <= k < oldTable.Length ==> oldTable[k] == old(hashTable[k]) // to prove post-condition
    {
      // to help proving ! full()
      countingLemma(oldTable, i, |valSet(oldTable, i)|, |delSet(oldTable, i)|, |nilSet(oldTable, i)|);

      if (oldTable[i].Some?) {
        insertAux(oldTable[i].value);
      }
    }

    // to help proving ! full()
    var i := oldTable.Length;
    countingLemma(oldTable, i, |valSet(oldTable, i)|, |delSet(oldTable, i)|, |nilSet(oldTable, i)|);
  }

  // Inserts a new value 'x' into this hash set.
  method insert(x : T)
    requires x !in elems
    ensures elems == old(elems) + {x}
  {
    if full() {
       rehash();
    }
    insertAux(x);
  }

  // Deletes an existent value 'x' from this hash set.
  method delete(x : T)
    requires x in elems
    ensures elems == old(elems) - {x}
 {
    var h := hash(x) % hashTable.Length;
    var i := locate(x);
    elems := elems - {x};
    hashTable[i] := Deleted;
    deleted := deleted + 1;
    used := used - 1;

    // to help proving that elems == valSet(hashTable, hashTable.Length)  
    assert forall k :: 0 <= k < hashTable.Length && k != i ==> hashTable[k] == old(hashTable[k]);

    // to help proving that deleted == |delSet()|
    assert delSet(hashTable, hashTable.Length) == old(delSet(hashTable, hashTable.Length)) + {i};
  }
}

method testHashSet() {
  var h := new HashSet<string>(x => |x|);
  assert h.elems == {};
  h.insert("Hello");
  assert h.elems == {"Hello"};
  h.insert("World");
  assert h.elems == {"Hello", "World"};
  var found := h.contains("Hello");
  assert found;
  found := h.contains("ANSI");
  assert !found;
  h.delete("Hello");
  assert h.elems == {"World"};
  found := h.contains("Hello");
  assert !found;
}
