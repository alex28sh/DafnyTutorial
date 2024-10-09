
// Now, let's see what changes Dafny from most of the languages - ability to write specifications

// let's define specifications for methods and functions from previous example 

method is_prime(n : nat) returns (b : bool) {
    if n == 1 {
        b := false;
    } else {
        var i := 2;
        b := true;
        while i < n
        {
            if n % i == 0 {
                b := false;
            }
            i := i + 1;
        }
    }
}

function not_divisible_on_prefix_func(n : nat, i : nat) : bool 
    requires n >= 2
    requires n >= i >= 2
    decreases n - i
{
    if i == n then true else if n % i == 0 then false else not_divisible_on_prefix_func(n, i + 1)
}

function is_prime_func(n : nat) : bool 
    requires n >= 2
{
    if n == 1 then false else not_divisible_on_prefix_func(n, 2)
}