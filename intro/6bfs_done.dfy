// It semms like, it will take half an hour


lemma in_visited(path : seq<int>, visited : set<int>) 
    requires |path| > 1 
    requires path[0] in visited
    requires path[|path| - 1] !in visited
    ensures exists i : int :: 0 <= i < |path| - 1 && path[i] in visited && path[i + 1] !in visited
{
    var i := 0;
    while i < |path| - 1
        invariant 0 <= i <= |path| - 1
        invariant forall j : int :: 0 <= j <= i ==> path[j] in visited
    {
        if path[i] in visited && path[i + 1] !in visited {
            return;
        }
        i := i + 1;
    }
}

lemma in_visited_forall(graph : seq<seq<int>>, visited : set<int>, start : int, end : int) 
    requires 0 <= start < |graph|
    requires 0 <= end < |graph|
    requires start != end
    requires start in visited 
    requires end !in visited
    requires forall i : int :: 0 <= i < |graph| ==> forall j : int :: 0 <= j < |graph[i]| ==> 0 <= graph[i][j] < |graph|
    ensures (forall p : seq<int> :: (|p| > 0 && p[0] == start && p[|p| - 1] == end && 
        (forall i : int :: 0 <= i < |p| ==> 0 <= p[i] < |graph|) && 
        forall i : int :: 0 <= i < |p| - 1 ==> p[i + 1] in graph[p[i]]) ==> 
        (|p| > 1 && exists i : int :: 0 <= i < |p| - 1 && p[i] in visited && p[i + 1] !in visited))
{
    forall p : seq<int> | (|p| > 0 && p[0] == start && p[|p| - 1] == end && 
        (forall i : int :: 0 <= i < |p| ==> 0 <= p[i] < |graph|) && 
        forall i : int :: 0 <= i < |p| - 1 ==> p[i + 1] in graph[p[i]]) 
        ensures (|p| > 1 && exists i : int :: 0 <= i < |p| - 1 && p[i] in visited && p[i + 1] !in visited)    
    {
        in_visited(p, visited);
    }
}

method bfs(graph : seq<seq<int>>, start : int, end : int) returns (b : bool)
    requires 0 <= start < |graph|
    requires 0 <= end < |graph|
    requires forall i : int :: 0 <= i < |graph| ==> forall j : int :: 0 <= j < |graph[i]| ==> 0 <= graph[i][j] < |graph|
    ensures b == (exists p : seq<int> :: |p| > 0 && p[0] == start && p[|p| - 1] == end && 
        (forall i : int :: 0 <= i < |p| ==> 0 <= p[i] < |graph|) && 
        forall i : int :: 0 <= i < |p| - 1 ==> p[i + 1] in graph[p[i]])
    decreases *
{
    if start == end {
        b := true;
        ghost var p : seq<int> := [start];
        assert (|p| > 0 && p[0] == start && p[|p| - 1] == end && 
            (forall i : int :: 0 <= i < |p| ==> 0 <= p[i] < |graph|) && 
            forall i : int :: 0 <= i < |p| - 1 ==> p[i + 1] in graph[p[i]]);
        
        return;
    }
    b := false;
    var q := [start];
    var visited : set<int> := {start};
    
    in_visited_forall(graph, visited, start, end);

    while |q| > 0
        invariant forall i : int :: 0 <= i < |q| ==> q[i] in visited
        invariant forall i : int :: 0 <= i < |q| ==> q[i] >= 0 && q[i] < |graph|    
        invariant forall i : int :: 0 <= i < |q| ==> q[i] in visited
        invariant end !in visited
        invariant forall e : int :: e in visited ==> (exists p : seq<int> :: |p| > 0 && p[0] == start && p[|p| - 1] == e && 
            (forall i : int :: 0 <= i < |p| ==> 0 <= p[i] < |graph|) && 
            forall i : int :: 0 <= i < |p| - 1 ==> p[i + 1] in graph[p[i]])
        invariant forall i, j : int :: 0 <= i < j < |q| ==> q[i] != q[j]
        invariant end !in visited
        invariant start in visited
        invariant (forall p : seq<int> :: (|p| > 0 && p[0] == start && p[|p| - 1] == end && 
            (forall i : int :: 0 <= i < |p| ==> 0 <= p[i] < |graph|) && 
            forall i : int :: 0 <= i < |p| - 1 ==> p[i + 1] in graph[p[i]]) ==> 
            (|p| > 1 && exists i : int :: 0 <= i < |p| - 1 && p[i] in visited && p[i + 1] !in visited))
        invariant (forall p : int :: |graph| > p >= 0 && p in visited && p !in q ==> (forall i : int :: 0 <= i < |graph[p]| ==> graph[p][i] in visited))
        decreases *
    {
        var node := q[0];
        q := q[1..];
        var neighbors := graph[node];
        var i := 0;
        while i < |neighbors|
            invariant 0 <= i <= |neighbors|
            invariant forall i : int :: 0 <= i < |q| ==> q[i] in visited
            invariant forall i : int :: 0 <= i < |q| ==> q[i] >= 0 && q[i] < |graph|    
            invariant forall j : int :: 0 <= j < i ==> neighbors[j] in visited
            invariant forall j : int :: 0 <= j < i ==> neighbors[j] in graph[node]
            invariant forall e : int :: e in visited ==> (exists p : seq<int> :: |p| > 0 && p[0] == start && p[|p| - 1] == e && 
                (forall i : int :: 0 <= i < |p| ==> 0 <= p[i] < |graph|) && 
                forall i : int :: 0 <= i < |p| - 1 ==> p[i + 1] in graph[p[i]])
            invariant forall i, j : int :: 0 <= i < j < |q| ==> q[i] != q[j]
            invariant forall x : int :: x in visited ==> 0 <= x < |graph|
            invariant end !in visited
            invariant start in visited
            invariant (forall j : int :: 0 <= j < i ==> (graph[node][j] in visited))
            invariant (forall p : seq<int> :: (|p| > 0 && p[0] == start && p[|p| - 1] == end && 
                (forall i : int :: 0 <= i < |p| ==> 0 <= p[i] < |graph|) && 
                forall i : int :: 0 <= i < |p| - 1 ==> p[i + 1] in graph[p[i]]) ==> 
                (|p| > 1 && exists i : int :: 0 <= i < |p| - 1 && p[i] in visited && p[i + 1] !in visited))
            invariant (forall p : int :: |graph| > p >= 0 && p in visited && p !in q && p != node ==> (forall i : int :: 0 <= i < |graph[p]| ==> graph[p][i] in visited))
            invariant (forall j : int :: 0 <= j < i ==> graph[node][j] in visited)
        {
            var neighbor := neighbors[i];
            if neighbor !in visited {
                ghost var p : seq<int> :| (|p| > 0 && p[0] == start && p[|p| - 1] == node && 
                    (forall i : int :: 0 <= i < |p| ==> 0 <= p[i] < |graph|) && 
                    forall i : int :: 0 <= i < |p| - 1 ==> p[i + 1] in graph[p[i]]);
                p := p + [neighbor];
                assert (|p| > 0 && p[0] == start && p[|p| - 1] == neighbor && 
                    (forall i : int :: 0 <= i < |p| ==> 0 <= p[i] < |graph|) && 
                    forall i : int :: 0 <= i < |p| - 1 ==> p[i + 1] in graph[p[i]]);
                visited := visited + {neighbor};
                if neighbor == end {
                    b := true;
                    return;
                }
                q := q + [neighbor];
            }
            i := i + 1;
            in_visited_forall(graph, visited, start, end);
        }
        in_visited_forall(graph, visited, start, end);
        assert (forall i : int :: 0 <= i < |graph[node]| ==> graph[node][i] in visited);
    }
}