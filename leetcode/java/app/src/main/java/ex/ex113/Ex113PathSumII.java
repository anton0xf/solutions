package ex.ex113;

import java.util.ArrayList;
import java.util.List;

/* https://leetcode.com/problems/path-sum-ii/ */
public class Ex113PathSumII {
    List<List<Integer>> paths = new ArrayList<>();
    List<Integer> prefix = new ArrayList<>();

    public List<List<Integer>> pathSum(TreeNode root, int targetSum) {
        if (root == null) {
            return List.of();
        }
        dfs(root, targetSum);
        return paths;
    }

    private void dfs(TreeNode node, int targetSum) {
        prefix.add(node.val);
        if (node.left == null && node.right == null) {
            if(node.val == targetSum) {
                paths.add(List.copyOf(prefix));
            }
        } else {
            if (node.left != null) {
                dfs(node.left, targetSum - node.val);
            }
            if (node.right != null) {
                dfs(node.right, targetSum - node.val);
            }
        }
        prefix.removeLast();
    }
}
