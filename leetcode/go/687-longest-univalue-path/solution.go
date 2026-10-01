package univaluepath

// https://leetcode.com/problems/longest-univalue-path

type TreeNode struct {
	Val   int
	Left  *TreeNode
	Right *TreeNode
}

func longestUnivaluePath(root *TreeNode) int {
	longestPath, _ := dfs(root, nil)
	return longestPath
}

func dfs(node *TreeNode, val *int) (int, int) {
	if node == nil {
		return 0, 0
	}
	longestLeft, heightLeft := dfs(node.Left, &node.Val)
	longestRight, heightRight := dfs(node.Right, &node.Val)
	longest := max(longestLeft, longestRight, heightLeft+heightRight)
	height := 0
	if val != nil && *val == node.Val {
		height = 1 + max(heightLeft, heightRight)
	}
	return longest, height
}
