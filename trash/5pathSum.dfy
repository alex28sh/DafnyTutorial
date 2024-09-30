datatype TreeNode = Nil | Tree(val: nat, left: TreeNode, right: TreeNode)

predicate isPath(paths: seq<TreeNode>, root: TreeNode) {
    if |paths| == 0 then false else match paths[0] {
        case Nil => false
        case Tree(val, left, right) => if |paths| == 1 then root == paths[0] else root == paths[0] && (isPath(paths[1..], left) || isPath(paths[1..], right))
    }
}

function pathSum(paths: seq<TreeNode>): nat {
    if |paths| == 0 then 0 else match paths[0] {
        case Nil => 0
        case Tree(val, left, right) => val + pathSum(paths[1..])
    }
}

method hasPathSum(root: TreeNode, targetSum: int) returns (b: bool) 
    ensures b ==> exists p: seq<TreeNode> :: isPath(p, root) && pathSum(p) == targetSum
{
    if root == Nil {
        return false;
    }

    if(root.val - targetSum == 0 && root.left == Nil && root.right == Nil) {
        assert isPath([root], root);
        assert pathSum([root]) == targetSum;
        return true;
    }
    var leftPath := hasPathSum(root.left, targetSum-root.val);
    var rightPath := hasPathSum(root.right, targetSum-root.val);

    assert rightPath ==> exists p: seq<TreeNode> :: isPath([root] + p, root) && pathSum(p) == targetSum-root.val;
    assert leftPath ==> exists p: seq<TreeNode> :: isPath([root] + p, root) && pathSum(p) == targetSum-root.val;
    
    return leftPath || rightPath;
}