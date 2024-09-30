predicate strictSorted(s : seq<int>) {
	forall u, w :: 0 <= u < w < |s| ==> s[u] < s[w]
}


method mcontained(v : seq<int>, w : seq<int>, n : int, m : int) returns (b : bool)
    requires n <= m && n >= 0
    requires strictSorted(v)
    requires strictSorted(w)
    requires |v| >= n && |w| >= m
    ensures b == forall k:: 0 <= k < n ==> v[k] in w[..m]
{
	var i:=0;
	var j:=0;
	while (i < n && j < m && (v[i] >= w[j]))
        invariant 0 <= i <= n
        invariant 0 <= j <= m
        invariant forall k:: 0 <= k < i ==> v[k] in w[..j] 
        invariant i < n ==> !(v[i] in w[..j])
	{	
		if (v[i] == w[j]) {
			i := i + 1;
		}
		j := j + 1;
		
	}
	b := i == n;
}

method Main() {
    print("Hello, world!" + "\n");
    var res := mcontained([1, 2, 3, 5], [1, 2, 3, 4, 5, 6], 3, 5);
    print res, "\n";
}