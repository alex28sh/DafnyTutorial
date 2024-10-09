
// Implement a method reverse which reverses an array of integers.

method reverse(a: array<int>) returns (b: array <int>)
  ensures b.Length == a.Length
  ensures forall i :: 0 <= i < a.Length ==> b[i] == a[a.Length - 1 - i]
{
  b := new int[a.Length];
  var i := 0;
  while i < a.Length

  {
    b[i] := a[a.Length - 1 - i];
    i := i + 1;
  }
}

// usually we want to reverse the array in place, without creating additional data structures
// in Dafny all input dynamic parameters (as arrays) by default cannot be modified
// to allow modification of an array, you need to add the `modifies` clause to the method signature
method reverse_inplace(a: array<int>)
  modifies a 
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
