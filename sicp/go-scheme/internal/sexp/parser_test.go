package sexp

import (
	"bytes"
	"errors"
	"testing"
	"testing/iotest"

	"github.com/stretchr/testify/assert"
)

func TestParser(t *testing.T) {
	t.Run("read error", func(t *testing.T) {
		p := NewParser(iotest.ErrReader(errors.New("fail")))
		_, eof, err := p.Parse()
		assert.False(t, eof, "EOF is not expected")
		assert.Error(t, err, "Unexpected error: fail")
	})

	t.Run("read char", func(t *testing.T) {
		p := NewParser(bytes.NewBufferString("a"))
		expr, eof, err := p.Parse()
		assert.True(t, eof, "EOF is expected")
		assert.NoError(t, err)
		assert.Equal(t, NewSeq("a"), expr)
	})

	t.Run("read char, stop at space", func(t *testing.T) {
		t.Skip()
		p := NewParser(bytes.NewBufferString("a "))
		expr, eof, err := p.Parse()
		assert.False(t, eof, "EOF is not expected")
		assert.NoError(t, err)
		assert.Equal(t, NewSeq("a"), expr)
	})

	t.Run("read chars", func(t *testing.T) {
		p := NewParser(bytes.NewBufferString("asdf"))
		expr, eof, err := p.Parse()
		assert.True(t, eof, "EOF is expected")
		assert.NoError(t, err)
		assert.Equal(t, NewSeq("asdf"), expr)
	})
}
