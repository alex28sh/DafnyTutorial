// 0. define TreeNode, path and pathSum
// 1. add asserts in if 
// 2. add asserts in second branch

// We have datatypes, as in Haskell, and we can do pattern matching!!!
datatype TreeNode = Nil | Tree(val: nat, left: TreeNode, right: TreeNode)

// we have a binary tree, lets` define what a path is
predicate isPath(path: seq<TreeNode>, root: TreeNode) {
    if |path| == 0 then false else match path[0] {
        case Nil => false
        case Tree(val, left, right) => if |path| == 1 then root == path[0] else root == path[0] && (isPath(path[1..], left) || isPath(path[1..], right))
    }
}

// path sum is calculated like a sum over sequence (like we have already seen in the previous examples)
function pathSum(path: seq<TreeNode>): nat {
    if |path| == 0 then 0 else match path[0] {
        case Nil => 0
        case Tree(val, left, right) => val + pathSum(path[1..])
    }
}

// this method returns true, if we found a path with the given sum, and false otherwise
method hasPathSum(root: TreeNode, targetSum: int) returns (b: bool) 
    ensures b ==> exists p: seq<TreeNode> :: isPath(p, root) && pathSum(p) == targetSum
    // we want to return true only if there exists a path in a tree that has the given sum 
{
    if root == Nil {
        return false;
    }

    if (root.val - targetSum == 0 && root.left == Nil && root.right == Nil) {
        assert isPath([root], root);
        assert pathSum([root]) == targetSum;
        // explicitly state that we found path (ask them)
        return true;
    }
    var leftPath := hasPathSum(root.left, targetSum-root.val);
    var rightPath := hasPathSum(root.right, targetSum-root.val);

    assert rightPath ==> exists p: seq<TreeNode> :: isPath([root] + p, root) && pathSum(p) == targetSum - root.val;
    assert leftPath ==> exists p: seq<TreeNode> :: isPath([root] + p, root) && pathSum(p) == targetSum - root.val;
    // rewrite postconditions for each of the subtrees (replace p by [root] + p, and root.left (right) by root)
    // ask them

    return leftPath || rightPath;
}