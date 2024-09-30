
// Implement a method reverse which reverses an array of integers.

method reverse(a: array<int>)
  modifies a // just denote that we can modify a, don't care about that
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[a.Length - 1 - i]) // old(x) - value of x in the begginning of the method
  // you can use old(x) also in asserts and invariants (it will also denote the value of x in the beginning of the method)
{
  var i := 0;
  while i < a.Length / 2
    
  {
    a[i], a[a.Length - 1 - i] := a[a.Length - 1 - i], a[i];
    i := i + 1;
  }
}