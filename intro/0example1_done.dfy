
// Now, let's see what changes Dafny from most of the languages - ability to write specifications

// let's define specifications for methods and functions from previous example 

predicate is_prime_pred(n : nat) // can define predicates (function that returns bool)
    requires n >= 1 // they may have preconditions, as well as postconditions
{ 
    n > 1 && forall i :: 2 <= i < n ==> n % i != 0
}

method is_prime(n : nat) returns (b : bool) 
    requires n >= 1 // pretty natural to suppose
    ensures b == is_prime_pred(n) // definition of prime number
{
    if n == 1 {
        b := false;
    } else {
        var i := 2;
        b := true;
        while i < n
            invariant 2 <= i <= n
            // standard practice is to define an invariant on the iterated variable
            invariant b == (n > 1 && forall j :: 2 <= j < i ==> n % j != 0)
            // prove postcondition iteratively 
        {
            if n % i == 0 {
                b := false;
            }
            i := i + 1;
        }
    }
}

function is_prime_func(n : nat, i : nat) : bool 
    requires n >= 2
    requires n > i >= 1
    ensures is_prime_func(n, i) == (forall j :: 2 <= j <= i ==> n % j != 0)
    // similar to invariant in the method is_prime
{
    if i == 1 then true else if n % i == 0 then false else is_prime_func(n, i - 1)
}

function is_prime_func_full(n : nat) : bool 
    requires n >= 1
    ensures is_prime_func_full(n) == is_prime_pred(n)
{
    if n == 1 then false else is_prime_func(n, n - 1)
}
