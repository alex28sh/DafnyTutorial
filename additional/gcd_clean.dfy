// Try to prove here that `exists q1: int :: q1 * result == a` and same for b.
// You can also try to prove `exists q1: int :: a % q1 == 0` (we found this task harder and don't know the solution)


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