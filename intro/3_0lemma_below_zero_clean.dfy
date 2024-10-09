// In this exercise, we will use lemmas, additional concept, helping to prove invariants.
// They remind the mathematical lemmas: they have some initial conditions and from them infer postconditions.


// We are verifying here the method below_zero, which checks if there is a prefix of the input sequence ops, 
// such that the sum of its elements is negative.

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
    ensures !res ==> forall i : int :: 0 <= i <= |ops| ==> psum(ops[..i]) >= 0
    ensures res ==> exists i : int :: 0 <= i <= |ops| && psum(ops[..i]) < 0
{
    var balance : int := 0;
    var i : int := 0;
    while (i < |ops|)
        invariant 0 <= i <= |ops| // as always
        invariant balance == psum(ops[..i])
        invariant forall j : int :: 0 <= j < i ==> psum(ops[..j]) >= 0
        // fill in the invariants
    {
        psum_property(ops, i);
        assert psum(ops[..i + 1]) == psum(ops[..i]) + ops[i];
        balance := balance + ops[i]; // psum(ops[..i+1])
        if (balance < 0) {
            return true;
        }
        i := i + 1;
    }
    return false;
}