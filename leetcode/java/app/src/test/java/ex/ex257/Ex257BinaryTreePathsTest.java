package ex.ex257;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.util.HashSet;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.*;

class Ex257BinaryTreePathsTest {
    private Ex257BinaryTreePaths solution = new Ex257BinaryTreePaths();

    private static TreeNode node(int val) {
        return new TreeNode(val);
    }

    private static TreeNode node(int val, TreeNode left, TreeNode right) {
        return new TreeNode(val, left, right);
    }

    @Test
    @DisplayName("root = [1,2,3,null,5]: two root-to-leaf paths, in any order")
    void example1() {
        TreeNode root = node(1, node(2, null, node(5)), node(3));
        assertEquals(Set.of("1->2->5", "1->3"), new HashSet<>(solution.binaryTreePaths(root)));
    }

    @Test
    @DisplayName("root = [1]: a single node is a path by itself")
    void example2() {
        assertEquals(Set.of("1"), new HashSet<>(solution.binaryTreePaths(node(1))));
    }
}
