package ex.ex113;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.*;

class Ex113PathSumIITest {
    private Ex113PathSumII solution = new Ex113PathSumII();

    private static TreeNode node(int val) {
        return new TreeNode(val);
    }

    private static TreeNode node(int val, TreeNode left, TreeNode right) {
        return new TreeNode(val, left, right);
    }

    @Test
    @DisplayName("root = [5,4,8,11,null,13,4,7,2,null,null,5,1]: two paths sum to 22, in any order")
    void example1() {
        TreeNode root = node(5,
                node(4, node(11, node(7), node(2)), null),
                node(8, node(13), node(4, node(5), node(1))));
        assertEquals(Set.of(List.of(5, 4, 11, 2), List.of(5, 8, 4, 5)),
                new HashSet<>(solution.pathSum(root, 22)));
    }

    @Test
    @DisplayName("root = [1,2,3]: no root-to-leaf path sums to 5")
    void example2() {
        assertEquals(List.of(), solution.pathSum(node(1, node(2), node(3)), 5));
    }

    @Test
    @DisplayName("root = [1,2]: the only root-to-leaf path is 1 -> 2 (sum 3), not 0")
    void example3() {
        assertEquals(List.of(), solution.pathSum(node(1, node(2), null), 0));
    }
}
