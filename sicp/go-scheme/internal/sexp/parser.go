package sexp

import (
	"bufio"
	"errors"
	"fmt"
	"io"
	"strconv"
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
	case '"':
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

	default:
		return ch, false, nil
	}
}
