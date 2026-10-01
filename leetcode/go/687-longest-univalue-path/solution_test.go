package univaluepath

import "testing"

func TestLongestUnivaluePath(t *testing.T) {
	tests := []struct {
		name string
		root *TreeNode
		want int
	}{
		{
			name: "example 1",
			root: &TreeNode{
				Val: 5,
				Left: &TreeNode{
					Val:   4,
					Left:  &TreeNode{Val: 1},
					Right: &TreeNode{Val: 1},
				},
				Right: &TreeNode{
					Val:   5,
					Right: &TreeNode{Val: 5},
				},
			},
			want: 2,
		},
		{
			name: "example 2",
			root: &TreeNode{
				Val: 1,
				Left: &TreeNode{
					Val:   4,
					Left:  &TreeNode{Val: 4},
					Right: &TreeNode{Val: 4},
				},
				Right: &TreeNode{Val: 5},
			},
			want: 2,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got := longestUnivaluePath(tt.root)
			if got != tt.want {
				t.Errorf("longestUnivaluePath() = %d, want %d", got, tt.want)
			}
		})
	}
}
