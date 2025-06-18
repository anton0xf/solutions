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

func (p *Parser) Parse() (Expr, bool, error) {
	ch, err := p.in.Next()
	if err != nil {
		if err == io.EOF {
			return nil, true, nil
		}
		return nil, false, err
	}
	return &Char{ch}, false, nil
}
