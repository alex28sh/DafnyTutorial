predicate IsSubstring(s: string, sub: string)
{
  |s| >= |sub| && exists i :: 0 <= i <= |s| - |sub| && s[i..i+|sub|] == sub
  // Here, you can see a warning about brittle verification
  // The cause is - possibly infinite number of formula instantiations
  // One way of overcoming this is to add so-called trigger expressions
  // like that: `exists i {:trigger s[i..i+|sub|]} :: 0 <= i <= |s| - |sub| && s[i..i+|sub|] == sub`
  // Trigger expressions take a crucial role in guiding the SMT solver towards a quick solution, 
  // by restricting the instantiations of a quantified assertion
  // You can think of them as a way to force solver to instantiate the quantified assertion only 
  // when the trigger expression occurs somewhere 
  // Bad triggers can also cause infinite instantiations, so it's important to choose them wisely
}

function RotateString(s: string, n: nat): string
  requires 0 <= n <= |s|
{
  s[n..] + s[..n]
}

method CycpatternCheck(word: string, pattern: string) returns (result: bool)
  ensures result ==> exists i :: 0 <= i <= |pattern| && IsSubstring(word, RotateString(pattern, i))
  ensures !result ==> forall i :: 0 <= i <= |pattern| ==> !IsSubstring(word, RotateString(pattern, i))
{
  var i := 0;
  while i <= |pattern|
    // add the invariants
  {
    if IsSubstring(word, RotateString(pattern, i)) {
      return true;
    }
    i := i + 1;
  }
  return false;
}