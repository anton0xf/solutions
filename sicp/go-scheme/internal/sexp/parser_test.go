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
		eof  bool
		expr Expr
		rest string
	}{
		{"read char", "a", true, NewSeq("a"), ""},
		// TODO {"read char, stop at space", "a ", true, NewSeq("a"), " "},
		{"read chars", "asdf", true, NewSeq("asdf"), ""},
	}
	for _, ex := range examples {
		t.Run(ex.name, func(t *testing.T) {
			in := bytes.NewBufferString(ex.in)
			p := NewParser(in)
			expr, eof, err := p.Parse()
			assert.Equal(t, ex.eof, eof)
			assert.NoError(t, err)
			assert.Equal(t, ex.expr, expr)
			assert.Equal(t, ex.rest, string(in.Bytes()))
		})
	}
}
