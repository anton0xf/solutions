package diameter

// https://leetcode.com/problems/diameter-of-binary-tree/description/

type TreeNode struct {
	Val   int
	Left  *TreeNode
	Right *TreeNode
}

func diameterOfBinaryTree(root *TreeNode) int {
	diameter, _ := dfs(root)
	return diameter
}

func dfs(node *TreeNode) (int, int) {
	if node == nil {
		return 0, 0
	}
	dl, hl := dfs(node.Left)
	dr, hr := dfs(node.Right)
	diameter := max(dl, dr, hl+hr)
	height := 1 + max(hl, hr)
	return diameter, height
}
