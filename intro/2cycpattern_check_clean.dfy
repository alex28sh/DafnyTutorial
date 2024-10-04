predicate IsSubstring(s: string, sub: string)
{
  |s| >= |sub| && exists i :: 0 <= i <= |s| - |sub| && s[i..i+|sub|] == sub
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