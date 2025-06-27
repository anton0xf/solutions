package sexp

import (
	"bufio"
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
	// TODO skip spaces
	// TODO loop
	seq := new(Seq)
	res = seq

	ch, eof, err := p.in.Next()
	if eof || err != nil {
		return
	}
	seq.Append(ch)

	return
}
