package sexp

import (
	"bytes"
	"errors"
	"fmt"
	"testing"
	"testing/iotest"

	"github.com/stretchr/testify/assert"
)

func TestParser_Parse(t *testing.T) {
	t.Run("read error", func(t *testing.T) {
		p := NewParser(iotest.ErrReader(errors.New("fail")))
		_, eof, err := p.Parse()
		assert.False(t, eof, "EOF is not expected")
		assert.EqualError(t, err, "Unexpected error: fail")
	})

	examples := []struct {
		name string
		in   string
		res  Expr
		rest string
	}{
		{"read empty", "", nil, ""},
		{"read 1-digit int", "1", &Int{1}, ""},
		{"read int", "123", &Int{123}, ""},
		{"read negative int", "-123", &Int{-123}, ""},
		{"read int, skip spaces", "\t 123", &Int{123}, ""},
		{"read int, stop at spaces", "123\na", &Int{123}, "\na"},
		{"read symbol", "qwer ty", &Symbol{"qwer"}, " ty"},
	}
	for _, ex := range examples {
		t.Run(ex.name, func(t *testing.T) {
			in := bytes.NewBufferString(ex.in)
			p := NewParser(in)
			res, eof, err := p.Parse()
			assert.Equal(t, ex.rest == "", eof)
			assert.NoError(t, err)
			assert.Equal(t, ex.res, res)
			rest, err := p.Rest()
			assert.NoError(t, err)
			assert.Equal(t, ex.rest, rest)
		})
	}

	errExamples := []struct {
		name string
		in   string
		err  string
		rest string
	}{
		{"digits+letters", "12ab ", "strconv.Atoi: parsing \"12ab\": invalid syntax", " "},
		{"unexpected minus", "1-2", "strconv.Atoi: parsing \"1-2\": invalid syntax", ""},
	}
	for _, ex := range errExamples {
		t.Run(ex.name, func(t *testing.T) {
			in := bytes.NewBufferString(ex.in)
			p := NewParser(in)
			res, eof, err := p.Parse()
			assert.Equal(t, ex.rest == "", eof)
			assert.EqualError(t, err, ex.err)
			assert.Nil(t, res)
			rest, err := p.Rest()
			assert.NoError(t, err)
			assert.Equal(t, ex.rest, rest)
		})
	}

}

func TestParser_ParseSeq(t *testing.T) {
	t.Run("read error", func(t *testing.T) {
		p := NewParser(iotest.ErrReader(errors.New("fail")))
		_, eof, err := p.ParseSeq()
		assert.False(t, eof, "EOF is not expected")
		assert.EqualError(t, err, "Unexpected error: fail")
	})

	examples := []struct {
		name string
		in   string
		res  []rune
		rest string
	}{
		{"read nothing", "", []rune{}, ""},
		{"read nothing, stop at spaces", "\n q", []rune{}, "\n q"},
		{"read char", "a", []rune("a"), ""},
		{"read char, stop at space", "a ", []rune("a"), " "},
		{"read chars", "asdf", []rune("asdf"), ""},
		{"read chars, stop at spaces", "asdf\nq", []rune("asdf"), "\nq"},
	}
	for _, ex := range examples {
		t.Run(ex.name, func(t *testing.T) {
			in := bytes.NewBufferString(ex.in)
			p := NewParser(in)
			res, eof, err := p.ParseSeq()
			assert.Equal(t, ex.rest == "", eof)
			assert.NoError(t, err)
			assert.Equal(t, ex.res, res)
			rest, err := p.Rest()
			assert.NoError(t, err)
			assert.Equal(t, ex.rest, rest)
		})
	}
}

func TestParser_SkipSpaces(t *testing.T) {
	t.Run("read error", func(t *testing.T) {
		p := NewParser(iotest.ErrReader(errors.New("fail")))
		eof, err := p.SkipSpaces()
		assert.False(t, eof, "EOF is not expected")
		assert.EqualError(t, err, "Unexpected error: fail")
	})

	examples := []struct {
		name string
		in   string
		rest string
	}{
		{"skip space", " a", "a"},
		{"skip spaces", " \t\nasdf\nq", "asdf\nq"},
	}
	for _, ex := range examples {
		t.Run(ex.name, func(t *testing.T) {
			in := bytes.NewBufferString(ex.in)
			p := NewParser(in)
			eof, err := p.SkipSpaces()
			assert.Equal(t, ex.rest == "", eof)
			assert.NoError(t, err)
			rest, err := p.Rest()
			assert.NoError(t, err)
			assert.Equal(t, ex.rest, rest)
		})
	}
}

func TestIsDigit(t *testing.T) {
	examples := []struct {
		r       rune
		isDigit bool
	}{
		{'0' - 1, false},
		{'0', true},
		{'1', true},
		{'5', true},
		{'9', true},
		{'9' + 1, false},
		{0x0663, false}, // ARABIC-INDIC DIGIT THREE
	}
	for _, ex := range examples {
		t.Run(fmt.Sprintf("'%c'", ex.r), func(t *testing.T) {
			assert.Equal(t, ex.isDigit, IsDigit(ex.r))
		})
	}
}
