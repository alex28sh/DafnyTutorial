function reverse(xs: seq<nat>): seq<nat>
{
    if xs == [] then [] else reverse(xs[1..]) + [xs[0]]
}

lemma ReverseAppendDistr(xs: seq<nat>, ys: seq<nat>)
    ensures reverse(xs + ys) == reverse(ys) + reverse(xs)
{
    if {
        case xs == [] => {
            calc {
                reverse([] + ys);
                calc {
                    [] + ys;
                    ys;
                }
                reverse(ys);
                reverse(ys) + reverse([]);
            }
        }
        case xs != [] => {
            var zs := xs + ys;
            assert reverse(zs) == reverse(zs[1..]) + [zs[0]];
            assert zs[1..] == xs[1..] + ys;
            assert reverse(xs + ys) == reverse(xs[1..] + ys) + [xs[0]];
        }
    }
}