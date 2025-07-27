package sexp

import (
	"bufio"
	"errors"
	"fmt"
	"io"
	"strconv"
	"strings"
	"unicode"
)

type Parser struct {
	in *RuneStream
}

func NewParser(in io.Reader) *Parser {
	return &Parser{
		&RuneStream{bufio.NewReader(in)},
	}
}

// TODO move the exprs hierarchy to a separate file
type Expr interface {
	String() string
}

func IsDigit(r rune) bool {
	return '0' <= r && r <= '9'
}

func IsIntString(rs []rune) bool {
	if rs == nil {
		return false
	}
	if len(rs) > 0 && IsDigit(rs[0]) {
		return true
	}
	if len(rs) > 1 && rs[0] == '-' && IsDigit(rs[1]) {
		return true
	}
	return false
}

type Int struct {
	x int
}

func (e *Int) String() string {
	return string(strconv.Itoa(e.x))
}

type Symbol struct {
	name string
}

func (e *Symbol) String() string {
	return e.name
}

type String struct {
	s string
}

func NewString(runes []rune) *String {
	return &String{string(runes)}
}

func (e *String) String() string {
	return fmt.Sprintf(`"%s"`, e.s)
}

type List struct {
	xs []Expr
}

func (e *List) String() string {
	var b strings.Builder
	b.WriteRune('(')
	for i, x := range e.xs {
		if i > 0 {
			b.WriteRune(' ')
		}
		b.WriteString(x.String())
	}
	b.WriteRune(')')
	return b.String()
}

type Quoted struct {
	x Expr
}

func (e *Quoted) String() string {
	return fmt.Sprintf("(quot %s)", e.x.String())
}

func (p *Parser) Parse() (res Expr, eof bool, err error) {
	eof, err = p.SkipSpaces()
	if eof || err != nil {
		return
	}
	runes, eof, err := p.ParseSeq()
	if err != nil {
		return
	}
	switch {
	case len(runes) == 0:
		return p.ParseDelimited()

	case IsIntString(runes):
		n, err := strconv.Atoi(string(runes))
		if err != nil {
			return nil, eof, err
		}
		return &Int{n}, eof, nil

	default:
		return &Symbol{string(runes)}, eof, nil
	}
}

func (p *Parser) SkipSpaces() (eof bool, err error) {
	for {
		ch, eof, err := p.in.Next()
		if eof || err != nil {
			return eof, err
		}
		if !unicode.IsSpace(ch) {
			p.in.UnreadRune()
			return false, nil
		}
	}
}

func (p *Parser) ParseSeq() (res []rune, eof bool, err error) {
	res = []rune{}
	for {
		ch, eof, err := p.in.Next()
		if eof || err != nil {
			return res, eof, err
		}
		if IsDelimiter(ch) {
			p.in.UnreadRune()
			return res, false, nil
		}
		res = append(res, ch)
	}
}

func IsDelimiter(ch rune) bool {
	switch ch {
	case '"', '\'', '(', ')':
		return true

	default:
		return unicode.IsSpace(ch)
	}
}

func (p *Parser) Rest() (string, error) {
	var res []rune
	for {
		ch, eof, err := p.in.Next()
		if eof || err != nil {
			return string(res), err
		}
		res = append(res, ch)
	}
}

func (p *Parser) Ignore(expected string) (eof bool, err error) {
	for _, ech := range expected {
		var ch rune
		ch, eof, err = p.in.Next()
		if eof || err != nil {
			return eof, err
		}
		if ch != ech {
			return eof, fmt.Errorf(
				"unexpected next char '%c'. expected '%c'", ch, ech)
		}
	}
	return eof, nil
}

func (p *Parser) ParseDelimited() (res Expr, eof bool, err error) {
	ch, eof, err := p.in.Next()
	if eof || err != nil {
		return nil, eof, err
	}
	switch ch {
	case '"':
		return p.ParseString()

	case '\'':
		return p.ParseQuoted()

	case '(':
		return p.ParseList()

	case ')': // TODO looks like a hack
		p.in.UnreadRune()
		return nil, false, nil

	default:
		return nil, eof, fmt.Errorf("unexpected next char: '%c'", ch)
	}
}

func (p *Parser) ParseString() (res *String, eof bool, err error) {
	rs := []rune{}
	for {
		ch, eof, err := p.in.Next()
		if err != nil {
			return NewString(rs), eof, err
		}

		if eof {
			return NewString(rs), eof, errors.New("unexpected EOF inside string")
		}

		switch ch {
		case '"':
			return NewString(rs), eof, err

		case '\\':
			ch, eof, err := p.ReadEscapedChar()
			if err != nil {
				return NewString(rs), eof, err
			}
			if eof {
				return NewString(rs), eof,
					errors.New("unexpected EOF inside escape sequence")
			}
			rs = append(rs, ch)

		default:
			rs = append(rs, ch)
		}
	}
}

func (p *Parser) ReadEscapedChar() (ch rune, eof bool, err error) {
	ch, eof, err = p.in.Next()
	if eof || err != nil {
		return
	}
	switch ch {
	case 'n':
		return '\n', false, nil

	case 't':
		return '\t', false, nil

	case 'u':
		return p.ReadUnicodeCode(4)

	case 'U':
		return p.ReadUnicodeCode(8)

	default:
		return ch, false, nil
	}
}

func (p *Parser) ReadUnicodeCode(size int) (ch rune, eof bool, err error) {
	var code uint64
	code, eof, err = p.ReadHex(size)
	if eof || err != nil {
		return
	}
	return rune(code), false, nil
}

func (p *Parser) ReadHex(size int) (res uint64, eof bool, err error) {
	for range size {
		var ch rune
		ch, eof, err = p.in.Next()
		if eof || err != nil {
			return
		}

		var d uint64 = 0

		switch {
		case '0' <= ch && ch <= '9':
			d = uint64(ch - '0')

		case 'a' <= ch && ch <= 'f':
			d = uint64(ch - 'a' + 10)

		case 'A' <= ch && ch <= 'F':
			d = uint64(ch - 'A' + 10)

		default:
			err = fmt.Errorf("Unexpected hex digit '%c'", ch)
			return
		}

		res = res*16 + d
	}
	return
}

func (p *Parser) ParseList() (res *List, eof bool, err error) {
	res = &List{nil}
	for {
		var expr Expr
		expr, eof, err = p.Parse()
		if eof || err != nil {
			return
		}

		if expr == nil {
			p.Ignore(")")
			return
		}

		res.xs = append(res.xs, expr)
	}
}

func (p *Parser) ParseQuoted() (res Expr, eof bool, err error) {
	var expr Expr
	expr, eof, err = p.Parse()
	if err != nil {
		return
	}

	if expr == nil {
		err = errors.New("ParseQuoted: unexpected nil expr")
		return
	}

	res = Quote(expr)
	return
}

func Quote(expr Expr) Expr {
	switch x := expr.(type) {
	case *Int, *String:
		return x

	case *List:
		if len(x.xs) == 0 {
			return &List{nil}
		}
		es := make([]Expr, len(x.xs))
		for i, e := range x.xs {
			es[i] = Quote(e)
		}
		return &List{es}

	default:
		return &Quoted{x}
	}
}
