// In previous examples of lemmas we used only equations and asserts.
// However, lemmas allow more broad functionality. 
// For example, we can iterate over the loop to prove postconditions of lemma (like in methods). 

// What makes this problem interesting is that the
// array we are searching in has two special properties: all elements are nonnegative, 
// and each successive element decreases by at most one from the
// previous element.

// a[i] >= 0
// a[i - 1] - 1 <= a[i] ~~  a[i] - d <= a[i + d] 
// find 0 
// a[i] != 0, j in [i, i + a[i]) -> a[j] != 0 --> i += a[i]

lemma {:axiom} SkippingLemma0(a: array<int>, j: int)
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 < i < a.Length ==> a[i - 1] - 1 <= a[i]
  requires 0 <= j < a.Length - 3

lemma {:axiom} SkippingLemma(a: array<int>, j: int) //  {:axiom} 
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 < i < a.Length ==> a[i - 1] - 1 <= a[i]
  requires 0 <= j < a.Length
  ensures forall i :: j <= i < j + a[j] && i < a.Length ==> a[i] != 0

method FindZero(a: array<int>) returns (index: int)
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 < i < a.Length ==> a[i - 1] - 1 <= a[i]
  requires exists i :: 0 <= i < a.Length && a[i] == 0
  ensures 0 <= index && index < a.Length && a[index] == 0
{
  index := 0;
  while index < a.Length
    // add invariants
  {
    if a[index] == 0 { return; }
    index := index + a[index];
  }
  index := -1;
}
