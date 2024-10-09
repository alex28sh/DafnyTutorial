
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
}


function not_divisible_on_prefix_func(n : nat, i : nat) : bool 
{
}

function is_prime_func(n : nat) : bool 
{
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
    
}