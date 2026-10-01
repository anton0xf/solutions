package diameter

import "testing"

func TestDiameterOfBinaryTree(t *testing.T) {
	tests := []struct {
		name string
		root *TreeNode
		want int
	}{
		{
			name: "example 1",
			root: &TreeNode{
				Val: 1,
				Left: &TreeNode{
					Val:   2,
					Left:  &TreeNode{Val: 4},
					Right: &TreeNode{Val: 5},
				},
				Right: &TreeNode{Val: 3},
			},
			want: 3,
		},
		{
			name: "example 2",
			root: &TreeNode{
				Val:  1,
				Left: &TreeNode{Val: 2},
			},
			want: 1,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got := diameterOfBinaryTree(tt.root)
			if got != tt.want {
				t.Errorf("diameterOfBinaryTree() = %d, want %d", got, tt.want)
			}
		})
	}
}
