// The Dafny "Hello, World!": a simple program for performing integer division.

// Computes the quotient 'q' and remainder 'r' of  the integer division of 
// a (non-negative) dividend 'n' by a (positive) divisor 'd'.
method div(n: nat, d: nat) returns (q: nat, r: nat)
  requires d > 0
  ensures q * d + r == n && r < d
{
  q := 0; 
  r := n;  
  while r >= d
    decreases r
    invariant q * d + r == n
  {
    q := q + 1;
    r := r - d;
  }
}

// Main program, with a simple test case (checked statically!)
method Main() {
    var q, r := div(15, 6);
    assert q == 2 && r == 3;
    print "q = ", q, " r=", r, "\n";
}
