// `sum_product` calculates the sum and product of a sequence of integers.
// Your task here is to prove sum and prop counting using the same method described previously

function sum(s: seq<int>) : int {
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}

lemma sum_prop(s: seq<int>)
    requires |s| > 0
    ensures sum(s) == sum(s[..|s| - 1]) + s[ |s| - 1 ]
{
    // fill in the proof
}

function prod(s: seq<int>) : int {
    if |s| == 0 then 1 else s[0] * prod(s[1..])
}

lemma prod_prop(s: seq<int>)
    requires |s| > 0
    ensures prod(s) == prod(s[..|s| - 1]) * s[ |s| - 1 ]
{
    // fill in the proof
}

method sum_product(numbers: seq<int>) returns (s : int, p : int)
    ensures s == sum(numbers)
    ensures p == prod(numbers)
 {
    s := 0;
    p := 1;
    for i := 0 to |numbers|
        // add invariants
    {
        // here, you can write auxiliary assertions about the sum and product
        s := s + numbers[i];
        p := p * numbers[i];
    }

    return s, p;
}