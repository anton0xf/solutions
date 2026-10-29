package ex.ex437;

/* https://leetcode.com/problems/path-sum-iii/ */
public class Ex437PathSumIII {
    public int pathSum(TreeNode root, int targetSum) {
        if (root == null) {
            return 0;
        }
        return dfs(root, targetSum);
    }

    private int dfs(TreeNode node, long targetSum) {
        int num = 0;
        if (node.val == targetSum) {
            num++;
        }
        if (node.left != null) {
            num += from(node.left, targetSum - node.val)
                    + dfs(node.left, targetSum);
        }
        if(node.right != null){
            num += from(node.right, targetSum - node.val)
                    + dfs(node.right, targetSum);
        }
        return num;
    }

    private int from(TreeNode node, long targetSum) {
        int num = 0;
        if (node.val == targetSum) {
            num++;
        }
        if (node.left != null) {
            num += from(node.left, targetSum - node.val);
        }
        if(node.right != null){
            num += from(node.right, targetSum - node.val);
        }
        return num;
    }
}
