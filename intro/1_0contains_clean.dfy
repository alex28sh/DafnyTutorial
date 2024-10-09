
// `mcontained` - checks if 1st sequence is contained in 2nd sequence
// sequences are strictly sorted

// seq<int> - data type for sequence of integers
// a : seq<int> 
// |a| - denotes length of sequence
// a[i] - refer to the i-th element of the sequence
// x in a, x !in a
// a[i..j]

method mcontained(v : seq<int>, w : seq<int>) returns (b : bool) 
{
	var i := 0;
	var j := 0;
	while (i < |v| && j < |w| && (v[i] > w[j]))
        // add here necessary invariants
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