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
	t.Run("error", func(t *testing.T) {
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
		eof  bool
	}{
		{"empty", "", nil, "", true},
		{"1-digit int", "1", &Int{1}, "", true},
		{"int", "123", &Int{123}, "", true},
		{"negative int", "-123", &Int{-123}, "", true},
		{"int, skip spaces", "\t 123", &Int{123}, "", true},
		{"int, stop at spaces", "123\na", &Int{123}, "\na", false},
		{"symbol", "qwer ty", &Symbol{"qwer"}, " ty", false},
		{"string", `"qwer"`, &String{"qwer"}, "", false},
		{"string with suffix", `"qwer" ty`, &String{"qwer"}, " ty", false},
		{"string, skip spaces",
			" \t\"qwer\" ty", &String{"qwer"}, " ty", false},
		{"string with spaces", ` "qw  er"ty`, &String{"qw  er"}, "ty", false},
		{"string with delims", ` "(qw)e'r"ty`, &String{"(qw)e'r"}, "ty", false},
		{"string with escaping",
			`"\n \t \a \"c" `, &String{"\n \t a \"c"}, " ", false},
		{"string with unicode escaping",
			`"\u0033 \u2713 \U0001f600"`, &String{"3 ✓ 😀"}, "", false},
		{"empty list", "()", NULL, "", false},
		{"list with number", "(1)a", NewList(&Int{1}), "a", false},
		{"list with 2 values",
			"(1 ab)", NewList(&Int{1}, &Symbol{"ab"}), "", false},
		{"list of list", "(())", NewList(NULL), "", false},
		{"list tree",
			"(1 ((3) 2))",
			NewList(&Int{1}, NewList(NewList(&Int{3}), &Int{2})), "", false},
		{"pair", "(1 . b )", Cons(&Int{1}, &Symbol{"b"}), "", false},
		{"pair with rest", "(1 . b) c", Cons(&Int{1}, &Symbol{"b"}), " c", false},
		{"dotted list", "(1 2 . 3)", Cons(&Int{1}, Cons(&Int{2}, &Int{3})), "", false},
		{"quoted int", "'12", &Int{12}, "", true},
		{"quoted symbol", "'ab", &Quoted{&Symbol{"ab"}}, "", true},
		{"quoted string", "' \"ab\"", &String{"ab"}, "", false},
		{"quoted empty list", "'()", &Quoted{NULL}, "", false},
		{"quoted list",
			"'(ab 3)", &Quoted{NewList(&Symbol{"ab"}, &Int{3})}, "", false},
		{"double-quoted int", "' '12", &Int{12}, "", true},
		{"double-quoted symbol",
			"''ab ", &Quoted{&Quoted{&Symbol{"ab"}}}, " ", false},
		{"quoted in list",
			"'(() '('ab 3))",
			&Quoted{NewList(
				NULL,
				&Quoted{NewList(&Quoted{&Symbol{"ab"}}, &Int{3})})},
			"", false},
	}
	for _, ex := range examples {
		t.Run(ex.name, func(t *testing.T) {
			in := bytes.NewBufferString(ex.in)
			p := NewParser(in)
			res, eof, err := p.Parse()
			assert.Equal(t, ex.eof, eof)
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
		rest string
		err  string
	}{
		{"digits+letters",
			"12ab ", " ",
			"strconv.Atoi: parsing \"12ab\": invalid syntax"},
		{"unexpected minus",
			"1-2", "",
			"strconv.Atoi: parsing \"1-2\": invalid syntax"},
		{"string unfinished",
			" \"asdf ", "",
			"ParseString: unexpected EOF inside string"},
		{"string unfinished escape sequence",
			" \"asdf \\", "",
			"ParseString: unexpected EOF inside escape sequence"},
		{"string wrong unicode escape sequesnce",
			" \"__\\u2fg__\" ", "__\" ",
			"ReadHex: unexpected hex digit 'g'"},
		// TODO error on unfinished list?
		{"pair without left part",
			"(. b)", " b)",
			"ParseList: illegal use of '.'"},
		{"pair without right part",
			"(a .)", ")",
			"ParseList: illegal use of '.'"},
	}
	for _, ex := range errExamples {
		t.Run(ex.name, func(t *testing.T) {
			in := bytes.NewBufferString(ex.in)
			p := NewParser(in)
			_, eof, err := p.Parse()
			assert.Equal(t, ex.rest == "", eof)
			assert.EqualError(t, err, ex.err)
			rest, err := p.Rest()
			assert.NoError(t, err)
			assert.Equal(t, ex.rest, rest)
		})
	}

}

func TestParser_ParseSeq(t *testing.T) {
	t.Run("error", func(t *testing.T) {
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
		{"nothing", "", []rune{}, ""},
		{"nothing, stop at spaces", "\n q", []rune{}, "\n q"},
		{"char", "a", []rune("a"), ""},
		{"char, stop at space", "a ", []rune("a"), " "},
		{"chars", "asdf", []rune("asdf"), ""},
		{"chars, stop at spaces", "asdf\nq", []rune("asdf"), "\nq"},
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
	t.Run("error", func(t *testing.T) {
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

func TestParser_Ignore(t *testing.T) {
	t.Run("error", func(t *testing.T) {
		p := NewParser(iotest.ErrReader(errors.New("fail")))
		eof, err := p.SkipSpaces()
		assert.False(t, eof, "EOF is not expected")
		assert.EqualError(t, err, "Unexpected error: fail")
	})

	examples := []struct {
		name string
		in   string
		s    string
		rest string
		err  string
	}{
		{"ignore on empty",
			"", "ab", "", "Parser: unexpected EOF. expected 'a'"},
		{"ignore",
			"abc___", "abc", "___", ""},
		{"ignore mismatch",
			"abc", "aw", "c", "Parser: unexpected next char 'b'. expected 'w'"},
	}
	for _, ex := range examples {
		t.Run(ex.name, func(t *testing.T) {
			in := bytes.NewBufferString(ex.in)
			p := NewParser(in)
			eof, err := p.Ignore(ex.s)
			assert.Equal(t, ex.rest == "", eof)
			if ex.err == "" {
				assert.NoError(t, err)
			} else {
				assert.EqualError(t, err, ex.err)
			}
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

func TestIsDelimiter(t *testing.T) {
	delims := " \t\n\"'()"
	notDelims := "01289abpuzABPUZ+-_"

	for _, ch := range delims {
		t.Run(fmt.Sprintf("delimiter '%c'", ch), func(t *testing.T) {
			assert.True(t, IsDelimiter(ch))
		})
	}

	for _, ch := range notDelims {
		t.Run(fmt.Sprintf("not delimiter '%c'", ch), func(t *testing.T) {
			assert.False(t, IsDelimiter(ch))
		})
	}
}

func TestParser_ReadHex(t *testing.T) {
	exs := []struct {
		size int
		in   string
		n    uint64
		eof  bool
		err  string
		rest string
	}{
		{1, "", 0, true, "", ""},
		{1, "Z", 0, false, "ReadHex: unexpected hex digit 'Z'", ""},
		{1, "/", 0, false, "ReadHex: unexpected hex digit '/'", ""}, // '0' - 1
		{1, "0", 0, false, "", ""},
		{1, "1", 1, false, "", ""},
		{1, "9", 9, false, "", ""},
		{1, ":", 0, false, "ReadHex: unexpected hex digit ':'", ""}, // '9' + 1
		{1, "`", 0, false, "ReadHex: unexpected hex digit '`'", ""}, // 'a' - 1
		{1, "a", 10, false, "", ""},
		{1, "f", 15, false, "", ""},
		{1, "g", 0, false, "ReadHex: unexpected hex digit 'g'", ""}, // 'f' + 1
		{1, "@", 0, false, "ReadHex: unexpected hex digit '@'", ""}, // 'A' - 1
		{1, "A", 10, false, "", ""},
		{1, "F", 15, false, "", ""},
		{1, "G", 0, false, "ReadHex: unexpected hex digit 'G'", ""}, // 'F' + 1

		{2, "a", 10, true, "", ""},
		{1, "ab", 10, false, "", "b"},
		{2, "1f?", 31, false, "", "?"},
	}
	for _, ex := range exs {
		t.Run(fmt.Sprintf("ReadHex(%d) on '%s'", ex.n, ex.in),
			func(t *testing.T) {
				in := bytes.NewBufferString(ex.in)
				p := NewParser(in)
				n, eof, err := p.ReadHex(ex.size)
				assert.Equal(t, ex.n, n)
				assert.Equal(t, ex.eof, eof)
				if len(ex.err) == 0 {
					assert.NoError(t, err)
				} else {
					assert.EqualError(t, err, ex.err)
				}
			})
	}
}
