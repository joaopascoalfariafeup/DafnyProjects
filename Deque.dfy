/* 
* Formal specification and verification of a double-ended-queue (DEQUE) with a bounded
* capacity implemented with a circular array, supporting the basic operations in time O(1).
* Illustrates the usage of ghost variables for state abstraction. 
* Difficulty: Low/Medium.
* FEUP, MIEIC, MFES, 2019/20.
*/


class {:autocontracts} Deque<T>
{
    // (Public) ghost variables used for specification purposes only
    ghost var elems: seq<T>  // front at head, back at tail
    ghost const capacity: nat 

    // (Private) concrete variables 
    const list: array<T> // circular array, from list[start] (front) to list[(start+size-1) % list.Length] (back) 
    var start : nat
    var size : nat

    ghost predicate Valid()
    {
        // integrity constraints on concrete representation 
        0 <= size <= list.Length  && 0 <= start < list.Length 
        // abstraction relation
        && capacity == list.Length 
        && elems == if start + size <= list.Length then list[start..start + size]
                    else list[start..] + list[..size - (list.Length - start)]  
    }
 
    constructor (capacity: nat, initialValue: T)
      requires capacity > 0
      ensures elems == [] && this.capacity == capacity
    {
        // initialize concrete variables
        list := new T[capacity]( _ => initialValue);
        start := 0;
        size := 0;
        // initialize ghost variables
        this.capacity := capacity;
        elems := []; 
    }

    predicate isEmpty()
      ensures isEmpty() <==> elems == []
    {
        size == 0
    }
    
    predicate isFull()
      ensures isFull() <==> |elems| == capacity
    {
        size == list.Length
    }

    function front() : T
      requires !isEmpty()
      ensures front() == elems[0]
    {
        list[start]
    }

    function back() : T
      requires !isEmpty()
      ensures back() == elems[|elems| - 1]
    {
        list[(start + size - 1) % list.Length] 
    }
    
    method push_back(x : T)
      requires !isFull()
      ensures elems == old(elems) + [x]
    {
        // update concrete variables
        list[(start + size) % list.Length] := x;
        size := size + 1;
        // update ghost variable
        elems := elems + [x];
    }

    method pop_back()
      requires !isEmpty()
      ensures elems == old(elems[..|elems|-1])
    {
        // update concrete variables
        size := size - 1;
        // update ghost variable
        elems := elems[..|elems|-1];
    }

    method push_front(x : T)
      requires !isFull()
      ensures elems == [x] + old(elems) 
    {
        // update concrete variables
        if start > 0
        {
            start := start - 1;
        }
        else
        {
            start := list.Length - 1;
        }
        list[start] := x;
        size := size + 1;
        // update ghost variable
        elems := [x] + elems;
    }    

    method pop_front()
      requires !isEmpty()
      ensures elems == old(elems[1..]) 
    {
        // update concrete variables
        if start + 1 < list.Length
        {
            start := start + 1;
        }
        else
        {
            start := 0;
        }
        size := size - 1;
        // update ghost variable
        elems := elems[1..];
    } 

}

// A simple test scneario.
method testDeque()
{
    var q := new Deque(3, 0);
    assert q.isEmpty();
    q.push_front(1);
    assert q.front() == 1;
    assert q.back() == 1;
    q.push_front(2);
    assert q.front() == 2;
    assert q.back() == 1;
    q.push_back(3);
    assert q.front() == 2;
    assert q.back() == 3;
    assert q.isFull();
    q.pop_back();
    assert q.front() == 2;
    assert q.back() == 1;
    q.pop_front();
    assert q.front() == 1;
    assert q.back() == 1;
    q.pop_front();
    assert q.isEmpty();
}
