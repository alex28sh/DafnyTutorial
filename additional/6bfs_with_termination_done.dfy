ghost predicate no_duplicates(xs: seq<int>)
{
    forall i, j :: 0 <= i < j < |xs| ==> xs[i] != xs[j]
}
ghost predicate is_node(graph: seq<seq<int>>, n: int)
{
    0 <= n < |graph|
}
ghost predicate is_graph(graph: seq<seq<int>>)
{
    forall i :: is_node(graph, i) ==>
        forall k {:trigger graph[i][k]} :: 0 <= k < |graph[i]| ==> is_node(graph, graph[i][k])
}
ghost predicate is_graph_path(graph: seq<seq<int>>, path: seq<int>)
{
    |path| > 0 &&
    (forall i :: 0 <= i < |path| ==> is_node(graph, path[i])) &&
    (forall i :: 0 <= i < |path| - 1 ==> path[i+1] in graph[path[i]])
}
ghost predicate path_ends_are(path: seq<int>, start: int, end: int)
{
    |path| > 0 && path[0] == start && path[|path|-1] == end
}
ghost predicate path_crosses(path: seq<int>, visited: set<int>)
{
    exists i :: 0 <= i < |path| - 1 && path[i] in visited && path[i+1] !in visited
}
ghost predicate valid_visited(graph: seq<seq<int>>, visited: set<int>)
{
    forall e :: e in visited ==> is_node(graph, e)
}
ghost predicate valid_queue(graph: seq<seq<int>>, q: seq<int>, visited: set<int>)
{
    (forall i :: 0 <= i < |q| ==> is_node(graph, q[i]) && q[i] in visited) && no_duplicates(q)
}
ghost predicate fully_visited(graph: seq<seq<int>>, e: int, visited: set<int>)
    requires is_node(graph, e)
{
    forall k :: k in graph[e] ==> k in visited
}
lemma in_visited(path : seq<int>, visited : set<int>) 
    requires |path| > 0 
    requires path[0] in visited
    requires path[|path| - 1] !in visited
    ensures path_crosses(path, visited)
{
    var i := 0;
    while i < |path| - 1
        invariant 0 <= i <= |path| - 1
        invariant forall j : int :: 0 <= j <= i ==> path[j] in visited
    {
        assert path[i] in visited;
        if path[i + 1] !in visited {
            return;
        }
        i := i + 1;
    }
}
lemma in_visited_forall(graph : seq<seq<int>>, visited : set<int>, start : int, end : int) 
    requires is_node(graph, start)
    requires is_node(graph, end)
    requires start in visited 
    requires end !in visited
    ensures forall p : seq<int> :: is_graph_path(graph, p) && path_ends_are(p, start, end) ==> path_crosses(p, visited)
{
    forall p : seq<int> | is_graph_path(graph, p) && path_ends_are(p, start, end)
        ensures path_crosses(p, visited)
    {
        in_visited(p, visited);
    }
}
lemma set_pigeonhole(n: nat, xs: set<int>)
    requires forall k :: k in xs ==> 0 <= k < n
    ensures |xs| <= n
{
    if (n > 0) {
        set_pigeonhole(n-1, xs - {n-1});
    }
}
lemma no_duplicates_seq_to_set(xs: seq<int>)
    requires no_duplicates(xs)
    ensures |set k | k in xs| == |xs|
{
    if |xs| > 0 {
        var s0 := set k | k in xs;
        var s1 := set k | k in xs[1..];
        assert s0 == s1 + {xs[0]};
        no_duplicates_seq_to_set(xs[1..]);
    }
}
lemma no_duplicates_seq_pigeonhole(n: nat, xs: seq<int>)
    requires forall k :: k in xs ==> 0 <= k < n
    requires no_duplicates(xs)
    ensures |xs| <= n
{
    set_pigeonhole(n, set k | k in xs);
    no_duplicates_seq_to_set(xs);
}
lemma queue_size_bound(graph: seq<seq<int>>, q: seq<int>, visited: set<int>)
    requires valid_queue(graph, q, visited)
    ensures |q| <= |graph|
{
    no_duplicates_seq_pigeonhole(|graph|, q);
}
lemma visited_size_bound(graph: seq<seq<int>>, visited: set<int>)
    requires valid_visited(graph, visited)
    ensures |visited| <= |graph|
{
    set_pigeonhole(|graph|, visited);
}
// This lemma is trivial, but splitting off the logic makes the verification go much faster.
lemma set_insertion(xs: seq<int>, s: set<int>, i: int)
    requires 0 <= i < |xs|
    requires forall j :: 0 <= j < i ==> xs[j] in s
    ensures forall j :: 0 <= j < i+1 ==> xs[j] in (s + {xs[i]})
{}
lemma set_insertion_trivial(xs: seq<int>, s: set<int>, i: int)
    requires 0 <= i < |xs|
    requires xs[i] in s
    requires forall j :: 0 <= j < i ==> xs[j] in s
    ensures forall j :: 0 <= j < i+1 ==> xs[j] in s
{}
lemma path_extend(graph: seq<seq<int>>, path: seq<int>, n: int)
    requires is_graph(graph)
    requires is_graph_path(graph, path)
    requires n in graph[path[|path|-1]]
    ensures is_graph_path(graph, path + [n])
{}
method bfs(graph : seq<seq<int>>, start : int, end : int) returns (b : bool)
    requires is_node(graph, start)
    requires is_node(graph, end)
    requires is_graph(graph)
    ensures b == exists p : seq<int> :: is_graph_path(graph, p) && path_ends_are(p, start, end)
    // decreases *
{
    if start == end {
        b := true;
        ghost var p : seq<int> := [start];
        assert is_graph_path(graph, p);
        assert path_ends_are(p, start, end);
        
        return;
    }
    b := false;
    var q := [start];
    var visited : set<int> := {start};
    
    assert is_graph_path(graph, [start]) && path_ends_are([start], start, start);
    in_visited_forall(graph, visited, start, end);
    ghost var unvisited := |graph| - 1;
    while |q| > 0
        invariant start in visited
        invariant end !in visited
        invariant valid_queue(graph, q, visited)
        invariant valid_visited(graph, visited)
        invariant forall e : int :: e in visited ==> exists p : seq<int> :: is_graph_path(graph, p) && path_ends_are(p, start, e)
        invariant forall p : seq<int> :: is_graph_path(graph, p) && path_ends_are(p, start, end) ==> path_crosses(p, visited)
        invariant forall e : int :: is_node(graph, e) && e in visited && e !in q ==> fully_visited(graph, e, visited)
        invariant unvisited == |graph| - |visited|
        invariant unvisited >= 0
        decreases |q| + unvisited
    {
        ghost var start_q := q;
        ghost var start_unvisited := unvisited;
        ghost var new_visited := 0;
        var node := q[0];
        q := q[1..];
        var neighbors := graph[node];
        var i := 0;
        while i < |neighbors|
            invariant 0 <= i <= |neighbors|
            invariant start in visited
            invariant end !in visited
            invariant valid_queue(graph, q, visited)
            invariant valid_visited(graph, visited)
            invariant forall e : int :: e in visited ==> exists p : seq<int> :: is_graph_path(graph, p) && path_ends_are(p, start, e)
            invariant forall j : int :: 0 <= j < i ==> neighbors[j] in visited
            invariant forall p : seq<int> :: is_graph_path(graph, p) && path_ends_are(p, start, end) ==> path_crosses(p, visited)
            invariant forall e : int :: is_node(graph, e) && e in visited && e !in q && e != node ==> fully_visited(graph, e, visited)
            invariant unvisited == |graph| - |visited|
            invariant |q| == |start_q| + new_visited - 1
            invariant unvisited == start_unvisited - new_visited
            invariant unvisited >= 0
        {
            var neighbor := neighbors[i];
            if neighbor !in visited {
                ghost var p : seq<int> :| is_graph_path(graph, p) && path_ends_are(p, start, node);
                path_extend(graph, p, neighbor);
                p := p + [neighbor];
                assert is_graph_path(graph, p);
                assert path_ends_are(p, start, neighbor);
                if neighbor == end {
                    b := true;
                    return;
                }
                q := q + [neighbor];
                set_insertion(neighbors, visited, i);
                visited := visited + {neighbor};
                unvisited := unvisited - 1;
                new_visited := new_visited + 1;
            } else {
                set_insertion_trivial(neighbors, visited, i);
            }
            i := i + 1;
            in_visited_forall(graph, visited, start, end);
            queue_size_bound(graph, q, visited);
            visited_size_bound(graph, visited);
            assert |q| + unvisited < |start_q| + start_unvisited;
        }
        in_visited_forall(graph, visited, start, end);
        assert (forall i : int :: 0 <= i < |graph[node]| ==> graph[node][i] in visited);
    }
}
