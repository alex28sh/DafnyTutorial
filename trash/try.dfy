
method non_term(a : nat) returns (b : nat)
    decreases 10 - a
{
    if a >= 10 {
        b := 0;
    } else {
        b := non_term(a + 1);
    }
}


function More(x: int): int {
    if x <= 0 then 1 else More(x - 2) + 3
}

lemma {:induction false} Increasing(x: int)
    ensures x < More(x)
{
    if x <= 0 {
    } else { 
        Increasing(x - 2);
        // assert x < More(x) by {
        //     calc {
        //         x - 2 < More(x - 2);
        //         x - 2 + 3 < More(x - 2) + 3;
        //         x + 1 < More(x);
        //         x < More(x) - 1;
        //         { assert More(x) - 1 < More(x); }
        //         { Increasing(x - 2); }
        //         x < More(x);
        //     }
        // }
    }
}

