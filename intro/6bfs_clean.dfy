
method {:axiom} bfs(graph : seq<seq<int>>, start : int, end : int) returns (b : bool)
    requires 0 <= start < |graph|
    requires 0 <= end < |graph|
    requires forall i : int :: 0 <= i < |graph| ==> forall j : int :: 0 <= j < |graph[i]| ==> 0 <= graph[i][j] < |graph|
    ensures b == (exists p : seq<int> :: |p| > 0 && p[0] == start && p[|p| - 1] == end && 
        (forall i : int :: 0 <= i < |p| ==> 0 <= p[i] < |graph|) && 
        forall i : int :: 0 <= i < |p| - 1 ==> p[i + 1] in graph[p[i]])
    decreases * // here, we don't want to prove termination
{
    if start == end {
        b := true;
        
        return;
    }
    b := false;
    var q := [start];
    var visited : set<int> := {start};
    

    while |q| > 0
        decreases * // don't want to prove cycle termination
    {
        var node := q[0];
        q := q[1..];
        var neighbors := graph[node];
        var i := 0;
        while i < |neighbors|
        {
            var neighbor := neighbors[i];
            if neighbor !in visited {
                visited := visited + {neighbor};
                if neighbor == end {
                    b := true;
                    return;
                }
                q := q + [neighbor];
            }
            i := i + 1;
        }
    }
}