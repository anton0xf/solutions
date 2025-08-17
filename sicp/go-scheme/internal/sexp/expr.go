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

// string reprecentation of nil Expr of any type
const NIL_STR = "<nil>"

type Int struct {
	x int
}

func (e *Int) String() string {
	// TODO check e for nil
	return string(strconv.Itoa(e.x))
}

type Symbol struct {
	name string
}

func (e *Symbol) String() string {
	// TODO check e for nil
	return e.name
}

type String struct {
	s string
}

func NewString(runes []rune) *String {
	return &String{string(runes)}
}

func (e *String) String() string {
	// TODO check e for nil
	return fmt.Sprintf(`"%s"`, e.s)
}

// Empty consed list and leaf of consed binary tree
type Null struct{}

func (*Null) String() string {
	// TODO check e for nil
	return "'()"
}

type Pair struct {
	x, y Expr
}

func Cons(x, y Expr) *Pair {
	// TODO check x and y for nil and panic?
	return &Pair{x, y}
}

func (e *Pair) String() string {
	if e == nil {
		return NIL_STR
	}
	return fmt.Sprintf("'(%v . %v)", e.x, e.y)
}

func (e *Pair) Car() (Expr, error) {
	if e == nil {
		return nil, fmt.Errorf("Car: Pair is %s", NIL_STR)
	}
	return e.x, nil
}

func (e *Pair) Cdr() (Expr, error) {
	if e == nil {
		return nil, fmt.Errorf("Cdr: Pair is %s", NIL_STR)
	}
	return e.y, nil
}

type List struct {
	// TODO it should be consed list.
	// It's impossible to implement default lists mutation behaviour using slice
	xs []Expr
}

func NewList(exprs ...Expr) *List {
	return &List{exprs}
}

func (e *List) Car() (Expr, error) {
	if e == nil {
		return nil, errors.New("Car: list is not initialized")
	} else if len(e.xs) == 0 {
		return nil, errors.New("Car: list is empty")
	}
	return e.xs[0], nil
}

func (e *List) String() string {
	if e == nil {
		return NIL_STR
	}

	var b strings.Builder
	b.WriteString("'(")
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
	if e == nil {
		return NIL_STR
	}

	var s string
	if e.x == nil {
		s = "<nil>"
	} else {
		s = e.x.String()
	}

	return fmt.Sprintf("'%s", s)
}
