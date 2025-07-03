package sexp

import (
	"bufio"
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

func IsIntString(rs []rune) bool {
	if rs == nil {
		return false
	}
	if len(rs) > 0 && unicode.IsDigit(rs[0]) {
		return true
	}
	if len(rs) > 1 && rs[0] == '-' && unicode.IsDigit(rs[1]) {
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
		return nil, eof, fmt.Errorf("unsupported. expected literal")

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
	// TODO parens etc.
	return unicode.IsSpace(ch)
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
