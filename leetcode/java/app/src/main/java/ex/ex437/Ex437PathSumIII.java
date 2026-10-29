package ex.ex437;

import java.util.Collections;
import java.util.List;
import java.util.stream.Stream;

/* https://leetcode.com/problems/path-sum-iii/ */
public class Ex437PathSumIII {
    public int pathSum(TreeNode root, int targetSum) {
        if (root == null) {
            return 0;
        }
        return dfs(root, targetSum, List.of((long)targetSum));
    }

    private int dfs(TreeNode node, long targetSum, List<Long> targetSums) {
        int num = 0;
        num += Collections.frequency(targetSums, (long)node.val);
        List<Long> sums = Stream.concat(Stream.of(targetSum),
                targetSums.stream().map(sum -> sum - node.val))
                .toList();
        if (node.left != null) {
            num += dfs(node.left, targetSum, sums);
        }
        if(node.right != null){
            num += dfs(node.right, targetSum, sums);
        }
        return num;
    }
}
