package sexp

import (
	"errors"
	"fmt"
	"strconv"
	"strings"
)

type Expr interface {
	String() string
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

func (e *List) Car() (Expr, error) {
	if e == nil {
		return nil, errors.New("car: list is not initialized")
	} else if len(e.xs) == 0 {
		return nil, errors.New("car: list is empty")
	}
	return e.xs[0], nil
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
