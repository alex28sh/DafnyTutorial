function gcd(a: int, b: int) : (result : int)
    requires a >= 0
    requires b >= 0
{
    if (b == 0) then a else
    if (a == 0) then b else
    if (a > b) then gcd(a % b, b) else
    if (b > a) then gcd(a, b % a) else a
}

lemma gcd_correct(a: int, b: int)
    requires a >= 0
    requires b >= 0

    ensures (exists q1:int :: (q1 * gcd(a,b) == a))
    ensures (exists q2:int :: (q2 * gcd(a,b) == b))
{
    if (b == 0) 
    {
        assert 1 * gcd(a,b) == a;
        assert 0 * gcd(a,b) == b;
    }
    else if (a == 0)
    {
        assert 1 * gcd(a,b) == b;
        assert 0 * gcd(a,b) == a;
    }
    else if (a > b)
    {
        gcd_correct(a % b, b);
        var q1 :| q1 * gcd(a % b,b) == a % b;
        var q2 :| q2 * gcd(a % b,b) == b;
        assert (q1+q2 * (a / b)) * gcd(a,b) == a;
    }
    else
    {
        gcd_correct(a, b % a);
        var q1 :| q1 * gcd(a,b % a) == b % a;
        var q2 :| q2 * gcd(a,b % a) == a;
        assert (q1+q2 * (b / a)) * gcd(a,b) == b;
    }
}

method greatest_common_divisor(a: nat, b: nat) returns (result: nat)
    requires a != 0 || b != 0
    ensures result == gcd(a, b)
    ensures (exists q1: int :: (q1 * result == a))
    ensures (exists q2: int :: (q2 * result == b))
{
    var x := a;
    var y := b;
    
 
    while (y != 0 && x != 0)
        decreases x+y
        invariant x >= 0
        invariant y >= 0
        invariant gcd(x,y) == gcd(a,b)
    {
        if x > y {
            x := x % y;
        } else {
            y := y % x;
        }
    }
    if x != 0 {
        result := x;
    } else {
        result := y;
    }
    gcd_correct(a,b);
}