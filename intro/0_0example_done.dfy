
// here, I should tell about basic functionality 

// Dafny - language that combines functional and imperative programming
// functional programming - pure functions and datatypes, coinductive datatypes, etc
// imperative programming - mutability, loops, etc
// Besides, Dafny contains specifications, such as preconditions, postconditions, invariants, termination metrics, etc  
// Also, it contains many constructs allowing more convenient and elegant proofs 


// function - well-defined, deterministic, pure 
// we cannot write cycles, cannot print anything, etc.
// method - body of statements that can mutate the state of the program


// let's write examples of functions and methods // here, I'm commenting 

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

// function cannot invoke a method, but a method can invoke a function
// function is_prime_func(n : nat) : bool 
//     requires n >= 2
// {
//     is_prime(n)
// }

method Main() {
    print("Hello, world!" + "\n");

    // running Main F5 (doesn't really differ)
    var is_prime_5 := is_prime(5);
    var is_prime_6 := is_prime(6);
    print(is_prime_5, "\n");
    print(is_prime_6, "\n");
}