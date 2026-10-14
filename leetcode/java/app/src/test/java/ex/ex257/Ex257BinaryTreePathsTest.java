package ex.ex257;

import org.junit.jupiter.api.Disabled;
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

    private void check(Set<String> expected, TreeNode root) {
        assertEquals(expected, new HashSet<>(solution.binaryTreePaths(root)));
    }

    @Test
    @DisplayName("root = [1,2,3,null,5]: two root-to-leaf paths, in any order")
    void example1() {
        TreeNode root = node(1, node(2, null, node(5)), node(3));
        check(Set.of("1->2->5", "1->3"), root);
    }

    @Test
    void empty() {
        check(Set.of(), null);
    }

    @Test
    @DisplayName("root = [1]: a single node is a path by itself")
    void example2() {
        check(Set.of("1"), node(1));
    }

    @Test
    void root() {
        check(Set.of("2"), node(2));
    }

    @Test
    void left() {
        check(Set.of("1->2"), node(1, node(2), null));
    }

    @Test
    void right() {
        check(Set.of("1->2"), node(1, null, node(2)));
    }

    @Test
    void both() {
        check(Set.of("1->2", "1->3"), node(1, node(2), node(3)));
    }

}
