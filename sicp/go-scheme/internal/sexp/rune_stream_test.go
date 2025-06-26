package sexp

import (
	"bytes"
	"errors"
	"testing"
	"testing/iotest"

	"github.com/stretchr/testify/assert"
)

func TestRuneStream(t *testing.T) {
	t.Run("error", func(t *testing.T) {
		s := NewRuneStream(iotest.ErrReader(errors.New("fail")))
		_, eof, err := s.Next()
		assert.False(t, eof, "EOF is not expected")
		assert.EqualError(t, err, "Unexpected error: fail")
	})

	t.Run("no chars", func(t *testing.T) {
		s := NewRuneStream(bytes.NewBufferString(""))
		_, eof, err := s.Next()
		assert.True(t, eof, "EOF is expected")
		assert.NoError(t, err)
	})

	t.Run("ascii char", func(t *testing.T) {
		s := NewRuneStream(bytes.NewBufferString("a"))
		ch, eof, err := s.Next()
		assert.False(t, eof, "EOF is not expected")
		assert.NoError(t, err)
		assert.Equal(t, 'a', ch)

		_, eof, err = s.Next()
		assert.True(t, eof, "EOF is expected")
		assert.NoError(t, err)
	})

	t.Run("cyrilic char", func(t *testing.T) {
		s := NewRuneStream(bytes.NewBufferString("ф"))
		ch, eof, err := s.Next()
		assert.False(t, eof, "EOF is not expected")
		assert.NoError(t, err)
		assert.Equal(t, 'ф', ch)

		_, eof, err = s.Next()
		assert.True(t, eof, "EOF is expected")
		assert.NoError(t, err)
	})
}
