
// 1 step - add invariant on index
// 2 step - asserts in `if` statement
// 3 step - add 2nd invariant
// 4 step - add assert `assert psum(ops[.. (i + 1)]) == psum(ops[.. i]) + ops[i]`
// 5 step - add last invariant
// 6 step - introduce calc (here, I'm just showing how to use it, unlike other steps)
// 7th step - prove psum_property with calc


// at the end I should say something about optimization
// you have cubid and quadratic solutions of dynamic programming task

lemma docalc(x : int, y: int)
  ensures (x + y) * (x + y) == x * x + 2 * x * y + y * y
{
  calc {
    (x + y) * (x + y);
    // distributive law: (a + b) * c == a * c + b * c
    x * (x + y) + y * (x + y);
    // distributive law: a * (b + c) == a * b + a * c
    x * x + x * y + y * x + y * y;
    calc {
	    y * x;
	    x * y;
    }
    x * x + x * y + x * y + y * y;
    calc {
      x * y + x * y;
      // a = 1 * a
      1 * x * y + 1 * x * y;
      // Distributive law
      (1 + 1) * x * y;
      2 * x * y;
    }
    x * x + 2 * x * y + y * y;
  }
}


function psum(s: seq<int>): int
{
    if |s| == 0 then 0
    else psum(s[ .. |s| - 1]) + s[|s| - 1]
}

lemma psum_property(s: seq<int>, i: int)
    requires 0 <= i < |s|
    ensures psum(s[.. (i + 1)]) == psum(s[.. i]) + s[i]
{
    calc == {
        psum(s[.. (i + 1)]);
        psum(s[.. (i + 1)][.. (i + 1) - 1]) + s[.. (i + 1)][(i + 1) - 1];
        { assert s[.. (i + 1)][.. (i + 1) - 1] == s[.. i]; }
        psum(s[.. i]) + s[i];
    }
}

method below_zero(ops: seq<int>) returns (res : bool)
    ensures !res ==> forall i : int :: 0 <= i <= |ops| ==> psum(ops[.. i]) >= 0
    ensures res ==> exists i : int :: 0 <= i <= |ops| && psum(ops[.. i]) < 0
{
    var balance : int := 0;
    var i : int := 0;
    while (i < |ops|)
        invariant 0 <= i <= |ops| // as always 
        invariant balance == psum(ops[.. i])
        invariant forall j : int :: 0 <= j <= i ==> psum(ops[.. j]) >= 0 // add this afer all other asserts and invariants
        // "see, first postconditions cannot be proved, let's add the invariants which 
        // reminds this postcondition, but holds for prefix"
        // "so, we prove postcondition inductively"
    {
        assert psum(ops[.. (i + 1)]) == psum(ops[.. i]) + ops[i] by {
            psum_property(ops, i);
        } // add this assert knowing about psum_property(ops, i)
        balance := balance + ops[i];
        if (balance < 0) {
            assert balance == psum(ops[.. i + 1]); // add this to show that we need 2nd invariant and 
            // assert `psum(ops[.. (i + 1)]) == psum(ops[.. i]) + ops[i]` is required
            assert psum(ops[.. i + 1]) < 0; // first, add this to show that we need previous assert
            return true;
        }
        i := i + 1;
    }

    return false;
}
