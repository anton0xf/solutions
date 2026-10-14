package ex.ex112;

import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class Ex112PathSumTest {
    private Ex112PathSum solution = new Ex112PathSum();

    private static TreeNode node(int val) {
        return new TreeNode(val);
    }

    private static TreeNode node(int val, TreeNode left, TreeNode right) {
        return new TreeNode(val, left, right);
    }

    @Test
    @DisplayName("root = [5,4,8,11,null,13,4,7,2,null,null,null,1]: the root-to-leaf path 5 -> 4 -> 11 -> 2 sums to 22")
    void example1() {
        TreeNode root = node(5,
                node(4, node(11, node(7), node(2)), null),
                node(8, node(13), node(4, null, node(1))));
        assertTrue(solution.hasPathSum(root, 22));
    }

    @Test
    @DisplayName("root = [1,2,3]: paths 1 -> 2 (sum 3) and 1 -> 3 (sum 4), no path with sum 5")
    void example2() {
        assertFalse(solution.hasPathSum(node(1, node(2), node(3)), 5));
    }

    @Test
    @DisplayName("root = []: the tree is empty, so there are no root-to-leaf paths")
    void example3() {
        assertFalse(solution.hasPathSum(null, 0));
    }

    @Test
    void oneOk() {
        assertTrue(solution.hasPathSum(node(1), 1));
    }

    @Test
    void oneFail() {
        assertFalse(solution.hasPathSum(node(1), 0));
    }

    @Test
    void leftOk() {
        assertTrue(solution.hasPathSum(node(1, node(2), null), 3));
    }

    @Test
    void leftFail() {
        assertFalse(solution.hasPathSum(node(1, node(2), null), 0));
    }

    @Test
    void rightFail() {
        assertFalse(solution.hasPathSum(node(1, null, node(2)), 1));
    }

    @Test
    void rightOk() {
        assertTrue(solution.hasPathSum(node(1, null, node(2)), 3));
    }

    @Test
    void bothOk() {
        assertTrue(solution.hasPathSum(node(1, node(10), node(2)), 3));
    }
}
