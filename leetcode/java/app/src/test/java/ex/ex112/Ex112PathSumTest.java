package ex.ex112;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class Ex112PathSumTest {
    private Ex112PathSum solution = new Ex112PathSum();

    @Test
    @DisplayName("root = [5,4,8,11,null,13,4,7,2,null,null,null,1]: the root-to-leaf path 5 -> 4 -> 11 -> 2 sums to 22")
    void example1() {
        TreeNode root = new TreeNode(5,
                new TreeNode(4,
                        new TreeNode(11, new TreeNode(7), new TreeNode(2)),
                        null),
                new TreeNode(8,
                        new TreeNode(13),
                        new TreeNode(4, null, new TreeNode(1))));
        assertTrue(solution.hasPathSum(root, 22));
    }

    @Test
    @DisplayName("root = [1,2,3]: paths 1 -> 2 (sum 3) and 1 -> 3 (sum 4), no path with sum 5")
    void example2() {
        TreeNode root = new TreeNode(1, new TreeNode(2), new TreeNode(3));
        assertFalse(solution.hasPathSum(root, 5));
    }

    @Test
    @DisplayName("root = []: the tree is empty, so there are no root-to-leaf paths")
    void example3() {
        assertFalse(solution.hasPathSum(null, 0));
    }
}
