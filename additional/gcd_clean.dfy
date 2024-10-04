// Try to prove here that `exists q1: int :: q1 * gcd == a` and same for b.


method greatest_common_divisor(a: nat, b: nat) returns (result: nat)
{
    var x := a;
    var y := b;
    
 
    while (y != 0 && x != 0)
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
}