package ex.ex257;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

/* https://leetcode.com/problems/binary-tree-paths/ */
public class Ex257BinaryTreePaths {
    List<String> paths = new ArrayList<>();
    List<String> prefix = new ArrayList<>();

    public List<String> binaryTreePaths(TreeNode root) {
        if (root == null) {
            return List.of();
        }
        dfs(root);
        return paths;
    }

    private void dfs(TreeNode node) {
        prefix.add(node.val + "");
        if (node.left == null && node.right == null) {
            paths.add(String.join("->", prefix));
            return;
        }
        if (node.left != null) {
            dfs(node.left);
            prefix.removeLast();
        }
        if (node.right != null) {
            dfs(node.right);
            prefix.removeLast();
        }
    }

}
