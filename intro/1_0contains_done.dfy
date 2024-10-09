
predicate strictSorted(s : seq<int>) {
	forall u, w :: 0 <= u < w < |s| ==> s[u] < s[w]
}

method mcontained(v : seq<int>, w : seq<int>) returns (b : bool)
    requires |v| <= |w|
    requires strictSorted(v)
    requires strictSorted(w)
    ensures b == forall k:: 0 <= k < |v| ==> v[k] in w
{
	var i := 0;
	var j := 0;
	while (i < |v| && j < |w| && (v[i] >= w[j])) // add (v[i] > w[j]) --> problem --> fix 
        invariant 0 <= i <= |v|
        invariant 0 <= j <= |w|
        // standard indices boundaries
        invariant forall k :: 0 <= k < i ==> v[k] in w[..j] 
        // subsequence v[..i] is contained in w[..j]
        invariant i < |v| ==> !(v[i] in w[..j])
        // due to the strictness, next element should not be in w[..j]
	{	
		if (v[i] == w[j]) {
			i := i + 1;
		}
		j := j + 1;
		
	}
	b := i == |v|;
}

method Main() {
    print("Hello, world!" + "\n");
    var res := mcontained([1, 2, 3, 5], [1, 2, 3, 4, 5, 6]);
    print res, "\n";
    var res1 := mcontained([1, 2, 3, 5], [1, 2, 3, 4, 5, 8]);
    print res1, "\n";
}