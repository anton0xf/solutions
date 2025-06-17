package fib

import "testing"

func TestFib(t *testing.T) {
	cases := []struct {
		n, f int
	}{
		{0, 0},
		{1, 1},
		{2, 1},
		{3, 2},
		{4, 3},
		{5, 5},
		{6, 8},
	}
	for _, c := range cases {
		got := Fib(c.n)
		if got != c.f {
			t.Errorf("Fib(%d) == %d, want %d", c.n, got, c.f)
		}
	}
}
