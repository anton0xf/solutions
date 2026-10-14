package ex.ex437;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class Ex437PathSumIIITest {
    private Ex437PathSumIII solution = new Ex437PathSumIII();

    private static TreeNode node(int val) {
        return new TreeNode(val);
    }

    private static TreeNode node(int val, TreeNode left, TreeNode right) {
        return new TreeNode(val, left, right);
    }

    @Test
    @DisplayName("root = [10,5,-3,3,2,null,11,3,-2,null,1]: paths 5 -> 3, 5 -> 2 -> 1 and -3 -> 11 sum to 8")
    void example1() {
        TreeNode root = node(10,
                node(5, node(3, node(3), node(-2)), node(2, null, node(1))),
                node(-3, null, node(11)));
        assertEquals(3, solution.pathSum(root, 8));
    }

    @Test
    @DisplayName("root = [5,4,8,11,null,13,4,7,2,null,null,5,1]: 3 downward paths sum to 22")
    void example2() {
        TreeNode root = node(5,
                node(4, node(11, node(7), node(2)), null),
                node(8, node(13), node(4, node(5), node(1))));
        assertEquals(3, solution.pathSum(root, 22));
    }
}
