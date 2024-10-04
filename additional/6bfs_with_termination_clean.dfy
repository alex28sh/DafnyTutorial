// While proving `bfs` together, we ommited proof of the termination. 
// Instead, we used `decreases *`, which states, that `while` cycle and method are possibly non-terminating and 
// Dafny don't need to prove termination. 
// Your task is to remove this statement and prove that the method `bfs` terminates.

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
    (forall i :: 0 <= i < |path| ==> is_node(graph, path[i])) &&
    (forall i :: 0 <= i < |path| - 1 ==> path[i+1] in graph[path[i]])
}

ghost predicate path_ends_are(path: seq<int>, start: int, end: int)
{
    |path| > 0 && path[0] == start && path[|path|-1] == end
}

method bfs(graph : seq<seq<int>>, start : int, end : int) returns (b : bool)
    requires is_node(graph, start)
    requires is_node(graph, end)
    requires is_graph(graph)
    ensures b == exists p : seq<int> :: is_graph_path(graph, p) && path_ends_are(p, start, end)
    decreases *
{
    if start == end {
        b := true;
        return;
    }
    b := false;
    var q := [start];
    var visited : set<int> := {start};

    while |q| > 0
        decreases *
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