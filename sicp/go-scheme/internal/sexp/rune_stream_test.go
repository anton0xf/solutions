package sexp

import (
	"testing"

	"go-scheme/internal/assert"
)

func TestRuneStream(t *testing.T) {
	t.Run("ascii char", func(t *testing.T) {
		s := NewRuneStreamFromBuffer([]byte("a"))
		ch, err := s.Next()
		assert.NoError(t, err)
		assert.EqRune(t, ch, 'a')
	})
}
