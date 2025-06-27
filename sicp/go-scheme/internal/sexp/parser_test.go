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

	examples := []struct {
		name string
		in   string
		expr Expr
		rest string
	}{
		{"read char", "a", NewSeq("a"), ""},
		{"read char, stop at space", "a ", NewSeq("a"), " "},
		{"read char, skip space", " a", NewSeq("a"), ""},
		{"read chars", "asdf", NewSeq("asdf"), ""},
		{"read chars, stop at spaces", "asdf\nq", NewSeq("asdf"), "\nq"},
		{"read chars inside spaces", " \tasdf\nq", NewSeq("asdf"), "\nq"},
	}
	for _, ex := range examples {
		t.Run(ex.name, func(t *testing.T) {
			in := bytes.NewBufferString(ex.in)
			p := NewParser(in)
			expr, eof, err := p.Parse()
			assert.Equal(t, ex.rest == "", eof)
			assert.NoError(t, err)
			assert.Equal(t, ex.expr, expr)
			rest, err := p.Rest()
			assert.NoError(t, err)
			assert.Equal(t, ex.rest, rest)
		})
	}
}
