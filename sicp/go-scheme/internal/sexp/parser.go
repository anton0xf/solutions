package sexp

import (
	"bufio"
	"fmt"
	"io"
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

type Char struct {
	ch rune
}

func (e *Char) String() string {
	return fmt.Sprintf("%c", e.ch)
}

func (p *Parser) Parse() (res Expr, eof bool, err error) {
	ch, eof, err := p.in.Next()
	if eof || err != nil {
		return
	}
	res = &Char{ch}
	return
}
