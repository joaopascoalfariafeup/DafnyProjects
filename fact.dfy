
/* 
* Formal specification and verification of factorials.
* FEUP, MIEIC, MFES, 2019/20.
*/

// Initial recursive definition of n!, space complexity O(n)
function fact(n: nat) : nat
  decreases n
{
    if n == 0 then 1 else n * fact(n-1)
}
// Iterative calculation of n!, space complexity O(1)
by method
{
  var f := 1;
  for i := 1 to n + 1 
    invariant f == fact(i-1)
  {
    f := f * i;
  }
  return f;
}

// Statically checked (proved) test cases!    
method testFact()
{
  assert fact(0) == 1;
  assert fact(1) == 1;
  assert fact(2) == 2;
  assert fact(3) == 6;
 }
