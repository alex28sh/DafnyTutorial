function psum(s: seq<int>): int
{
    if |s| == 0 then 0
    else psum(s[ .. |s| - 1]) + s[|s| - 1]
}

lemma {:axiom} docalc(x : int, y: int)
  ensures (x + y) * (x + y) == x * x + 2 * x * y + y * y
// {
//     // uncomment, remove {:axiom}, and fill in the proof
//     // prove the lemma
// }

lemma {:axiom} psum_property(s: seq<int>, i: int) // axiom - don't need to prove
    requires 0 <= i < |s|
    ensures psum(s[.. (i + 1)]) == psum(s[.. i]) + s[i]
// {
//     // uncomment, remove {:axiom}, and fill in the proof
//     // prove the lemma
// }

method below_zero(ops: seq<int>) returns (res : bool)
    ensures res ==> forall i : int :: 0 <= i <= |ops| ==> psum(ops[..i]) >= 0
    ensures !res ==> exists i : int :: 0 <= i <= |ops| && psum(ops[..i]) < 0
{
    var balance : int := 0;
    var i : int := 0;
    while (i < |ops|)
        // fill in the invariants
    {
        // use assert
        balance := balance + ops[i];
        if (balance < 0) {
            return false;
        }
        i := i + 1;
    }
    return true;
}