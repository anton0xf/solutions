package sexp

import (
	"bufio"
	"io"
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

type Seq struct {
	chs []rune
}

func NewSeq(s string) *Seq {
	return &Seq{[]rune(s)}
}

func (e *Seq) Append(ch rune) {
	e.chs = append(e.chs, ch)
}

func (e *Seq) String() string {
	return string(e.chs)
}

func (p *Parser) Parse() (res Expr, eof bool, err error) {
	eof, err = p.SkipSpaces()
	if eof || err != nil {
		return
	}
	return p.ParseSeq()
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

func (p *Parser) ParseSeq() (res *Seq, eof bool, err error) {
	var seq Seq
	res = &seq
	for {
		ch, eof, err := p.in.Next()
		if eof || err != nil {
			return res, eof, err
		}
		if IsDelimiter(ch) {
			p.in.UnreadRune()
			return res, false, nil
		}
		seq.Append(ch)
	}
}

func IsDelimiter(ch rune) bool {
	// TODO parents etc.
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
