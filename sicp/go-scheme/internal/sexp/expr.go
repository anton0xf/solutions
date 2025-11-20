package sexp

import (
	"fmt"
	"strconv"
)

type Expr interface {
	// Get string representation of expression
	String() string
}

// string reprecentation of nil Expr of any type
const NIL_STR = "<nil>"

type Int struct {
	x int
}

func (e *Int) String() string {
	if e == nil {
		return NIL_STR
	}
	return string(strconv.Itoa(e.x))
}

type Symbol struct {
	name string
}

func (e *Symbol) String() string {
	if e == nil {
		return NIL_STR
	}
	return e.name
}

type String struct {
	s string
}

func NewString(runes []rune) *String {
	return &String{string(runes)}
}

func (e *String) String() string {
	if e == nil {
		return NIL_STR
	}
	return fmt.Sprintf(`"%s"`, e.s)
}

// Empty consed list and leaf of consed binary tree
type Null struct{}

var NULL = &Null{}

func (e *Null) String() string {
	if e == nil {
		return NIL_STR
	}
	return "()"
}

type Pair struct {
	x, y Expr
}

func Cons(x, y Expr) *Pair {
	return &Pair{x, y}
}

func pairString(x, y Expr) string {
	if y == nil {
		return fmt.Sprintf("%v . %s", x, NIL_STR)
	}
	switch yt := y.(type) {
	case *Null:
		return x.String()
	case *Pair:
		return fmt.Sprintf("%v %s", x, pairString(yt.x, yt.y))
	default:
		return fmt.Sprintf("%v . %v", x, y)
	}
}

func (e *Pair) String() string {
	if e == nil {
		return NIL_STR
	}
	return fmt.Sprintf("(%s)", pairString(e.x, e.y))
}

func Car(expr Expr) (Expr, error) {
	if expr == nil {
		return nil, fmt.Errorf("Car: Pair is %s", NIL_STR)
	}
	switch e := expr.(type) {
	case *Pair:
		return e.x, nil

	default:
		return nil,
			fmt.Errorf("Car: wrong argument type (pair expected): %s", expr)
	}
}

func (e *Pair) Cdr() (Expr, error) {
	if e == nil {
		return nil, fmt.Errorf("Cdr: Pair is %s", NIL_STR)
	}
	return e.y, nil
}

func NewList(exprs ...Expr) Expr {
	return NewListWithTail(exprs, NULL)
}

func NewListWithTail(exprs []Expr, tail Expr) Expr {
	var res Expr = tail
	cur := &res
	for _, e := range exprs {
		p := Cons(e, tail)
		*cur = p
		cur = &p.y
	}
	return res
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
