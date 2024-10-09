// 1. Introduce algorithm, visited variable, so on
// 2. Introduce 1-4 predicates
// 3. Solve case with start == end (ask)
// 4. Observe the problem here: (ask)
//      var neighbors := graph[node]; // out of bounds 
//    Add valid_queue predicate in invariants
// 5. Add standard index invariant in the inner cycle (it seems, it can prove without it)
// 6. Look at the return statement: postcondition cannot be proven there 
//    // (not a part of a plan) Do we need to split equation into 2 implications?
//    The intuiton here - is that for all visited vertices we should prove that there is a path from start to this vertex
//    Let's add such invariants 
// 7. Invariant in the outer loop cannot be proven on enty (ask what to do)
//    Let's add a necessary assertion
// 8. Inner invariant cannot be proven to be maintained
//    Let's try to observe how it's behaving when adding a new vertex into visited
//    Add assertion
//    It cannot be proven 
//    What can we do (hint we don't need any invariants - only assertions and ghost variables here)? 
//    Let's pick up path `p`, statisfying same condition for node, and try to make transition to `p + [neighbor]`
//    Add interesting assertions
//    See, it can be proven
// 9. Now, we have to prove same postcondition, but for case, when path does not exist 
//    So, we want to prove smth like `(exists p : seq<int> :: is_graph_path(graph, p) && path_ends_are(p, start, end)) ==> false`
//    Let's add this assertion at the end, and make sure, it cannot be proven 
//    It can be reformulated like `forall p : seq<int> :: is_graph_path(graph, p) && path_ends_are(p, start, end) ==> false`
//    It seems like here we should prove some contradiction for existing path to the end 
//    Let's try to find out contradict assumptions (ask them)
//    First: in each path there is a couple of consequent vertices, one of them is visited, and another is not (if start is visited and end is not)
//    Second: if vertex is visited and already processed, then all its neighbors are visited
//    (Explain them graphically)
// 10. Add these contradictions as invariants
//     Both cannot be proven
// 11. Let's try to prove second (ask them?)
//     Prove by just adding help invariant to the inner loop (usual trick)
// 12. Come back to the first assumption
//     Try to state lemma explicitely and add into the end of each cycle
// 13. Ask them to suggest how to prove `in_visited_forall` 
//     Fill in `in_visited_forall` (also stating `in_visited`, but not proving)
// 14. Ask them to prove `in_visited` (hint: use cycle and invariant)
// 15. It seems like, thats all!


ghost predicate is_node(graph: seq<seq<int>>, n: int)
{
    0 <= n < |graph|
}

ghost predicate is_graph(graph: seq<seq<int>>)
{
    forall i :: is_node(graph, i) ==>
        forall k :: 0 <= k < |graph[i]| ==> is_node(graph, graph[i][k])
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
    (forall i :: 0 <= i < |q| ==> is_node(graph, q[i]) && q[i] in visited) &&
    (forall i, j :: 0 <= i < j < |q| ==> q[i] != q[j])
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
    // ghost var p : seq<int> :| is_graph_path(graph, p) && path_ends_are(p, start, end);
    // in_visited(p, visited);
    forall p : seq<int> | is_graph_path(graph, p) && path_ends_are(p, start, end)
        ensures path_crosses(p, visited)
    {
        in_visited(p, visited);
    }
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

    while |q| > 0
        invariant start in visited
        invariant end !in visited
        invariant valid_queue(graph, q, visited)
        invariant valid_visited(graph, visited)
        invariant forall e : int :: e in visited ==> exists p : seq<int> :: is_graph_path(graph, p) && path_ends_are(p, start, e)
        invariant forall p : seq<int> :: is_graph_path(graph, p) && path_ends_are(p, start, end) ==> path_crosses(p, visited)
        invariant forall n : int :: is_node(graph, n) && n in visited && n !in q ==> (forall i : int :: 0 <= i < |graph[n]| ==> graph[n][i] in visited)
        decreases *
    {
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
            invariant forall n : int :: is_node(graph, n) && n in visited && n !in q && n != node ==> (forall i : int :: 0 <= i < |graph[n]| ==> graph[n][i] in visited)
        {
            var neighbor := neighbors[i];
            if neighbor !in visited {
                ghost var p : seq<int> :| is_graph_path(graph, p) && path_ends_are(p, start, node);
                p := p + [neighbor];
                assert is_graph_path(graph, p) && path_ends_are(p, start, neighbor);
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
    assert forall p : seq<int> :: is_graph_path(graph, p) && path_ends_are(p, start, end) ==> path_crosses(p, visited);
    assert forall p : seq<int> :: is_graph_path(graph, p) && path_ends_are(p, start, end) ==> false;
}