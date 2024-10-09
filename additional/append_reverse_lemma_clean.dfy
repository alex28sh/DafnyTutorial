function reverse(xs: seq<nat>): seq<nat>
{
    if xs == [] then [] else reverse(xs[1..]) + [xs[0]]
}

lemma ReverseAppendDistr(xs: seq<nat>, ys: seq<nat>)
    ensures reverse(xs + ys) == reverse(ys) + reverse(xs)
{
    if { // pattern-matching on xs
        case xs == [] => { 
            // fill in the proof here
        }
        case xs != [] => {
            // fill in the proof here
        }
    }
}