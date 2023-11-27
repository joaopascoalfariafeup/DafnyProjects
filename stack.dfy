/* 
* Formal specification and verification of a Stack with limited capacity.
* Used to illustration the verification of object-oriented programs.
* Defficulty: Low.
* TODO: Dynamic capacity.
* FEUP, MIEIC, MFES, 2019/20.
*/

class {:autocontracts} Stack<T>
{
    const elems: array<T>; // immutable (pointer)
    var size : nat; // used size

    ghost predicate Valid()
    {
        size <= elems.Length
    }
 
    constructor (capacity: nat, initialValue: T)
      requires capacity > 0
      ensures elems.Length == capacity && size == 0
    {
        elems := new T[capacity](_ => initialValue);
        size := 0; 
    }

    predicate  isEmpty()
    {
        size == 0
    }
    
    predicate  isFull()
    {
        size == elems.Length
    }

    method push(x : T)
      requires !isFull()
      ensures elems[..size] == old(elems[..size]) + [x]
    {
        elems[size] := x;
        size := size + 1;
    }

    function  top() : T
      requires !isEmpty()
    {
         elems[size-1]
    }
    
    method pop() 
      requires !isEmpty()
      ensures elems[..size] == old(elems[..size-1])
    {
         size := size-1;
    }
}

// A simple test case.
method testStack()
{
    var s := new Stack(3, 0);
    assert s.isEmpty();
    s.push(1);
    s.push(2);
    s.push(3);
    assert s.top() == 3;
    assert s.isFull();
    s.pop();
    assert s.top() == 2;
    print "top = ", s.top(), " \n";
}
