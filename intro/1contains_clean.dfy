
// Now, try to verify method on your own 
// Add necessary invariants to the cycle below 

predicate strictSorted(s : seq<int>) {
	forall u, w :: 0 <= u < w < |s| ==> s[u] < s[w]
}

// seq<int> - data type for sequence of integers
// a : seq<int> 
// |a| - denotes length of sequence
// a[i] - refer to the i-th element of the sequence
// x in a, x !in a
// a[i..j]

method mcontained(v : seq<int>, w : seq<int>) returns (b : bool) 
    requires |v| <= |w|
    requires strictSorted(v)
    requires strictSorted(w)
    ensures b == forall k:: 0 <= k < |v| ==> v[k] in w
{
	var i := 0;
	var j := 0;
	while (i < |v| && j < |w| && (v[i] >= w[j]))
        // add here necessary invariants
	{	
		if (v[i] == w[j]) {
			i := i + 1;
		}
		j := j + 1;
		
	}
	b := i == |v|;
}
