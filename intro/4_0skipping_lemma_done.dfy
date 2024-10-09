
// It will be great to diskuss the problem graphically (draw pictures bla bla bla)
// And understand why postconditions are really true

// We need to prove only 1st invariant. 
// Add invariant on index
// Add invariant resembling postcondition
// Go to 0 lemma to show what we want 
// Write cycle in lemma
// Add invarant resembling postcondition
// Discuss, which invariant we need to prove, and ad 1st invariant

lemma SkippingLemma0(a: array<int>, j: int) // just showing 
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 < i < a.Length ==> a[i - 1] - 1 <= a[i]
  requires 0 <= j < a.Length - 3
  // Note: the above has been changed so that the array indices below are good. 
{
  assert a[j] - 1 <= a[j + 1];
  assert a[j + 1] - 1 <= a[j + 2];
  assert a[j + 2] - 1 <= a[j + 3];
  // therefore:
  assert a[j] - 3 <= a[j + 3];
}

lemma SkippingLemma(a: array<int>, j: int) //  {:axiom} 
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 < i < a.Length ==> a[i - 1] - 1 <= a[i]
  requires 0 <= j < a.Length
  ensures forall i :: j <= i < j + a[j] && i < a.Length ==> a[i] != 0
{
  var i := j;
  while i < j + a[j] && i < a.Length
    invariant i < a.Length ==> a[j] - (i - j) <= a[i]
    invariant forall k :: j <= k < i && k < a.Length ==> a[k] != 0
  {
    i := i + 1;
  }
}

method FindZero(a: array<int>) returns (index: int)
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 < i < a.Length ==> a[i - 1] - 1 <= a[i]
  ensures index < 0  ==> forall i :: 0 <= i < a.Length ==> a[i] != 0
  ensures 0 <= index ==> index < a.Length && a[index] == 0
{
  index := 0;
  while index < a.Length
    invariant 0 <= index
    invariant forall k :: 0 <= k < index && k < a.Length ==> a[k] != 0
  {
    if a[index] == 0 { return; }
    SkippingLemma(a, index);
    index := index + a[index];
  }
  index := -1;
}