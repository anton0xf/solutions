package assert

import "testing"

func NoError(t *testing.T, err error) {
	if err != nil {
		t.Errorf("unexpected error: %v", err)
	}
}

func EqRune(t *testing.T, actual rune, expected rune) {
	if actual != expected {
		t.Errorf("unexpected rune %c. expected %c",
			actual, expected)
	}
}
