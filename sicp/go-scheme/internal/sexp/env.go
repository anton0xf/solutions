package sexp

import (
	"errors"
	"fmt"
)

type Env struct{}

func (env *Env) Eval(expr Expr) (Expr, error) {
	switch e := expr.(type) {
	case *Int, *String:
		return e, nil

	case *Symbol:
		return nil, fmt.Errorf(
			"Eval: Symbol parameter is not supported yet: %v", e)

	case *Quoted:
		return EvalQuoted(e)

	case *List:
		return EvalList(e)

	default:
		return nil, fmt.Errorf(
			"Eval: unexpected type %T of parameter %v", expr, expr)
	}
}

func EvalQuoted(e *Quoted) (Expr, error) {
	if e == nil {
		return nil, errors.New("EvalQuoted: nil parameter")
	}

	if e.x == nil {
		return nil, errors.New("EvalQuoted: Quoted{nil}")
	}

	switch x := e.x.(type) {
	case *Int, *String:
		return x, nil

	default:
		return e, nil
	}
}

func EvalList(e *List) (Expr, error) {
	if e == nil {
		return nil, errors.New("EvalList: nil parameter")
	}

	if len(e.xs) == 0 {
		return nil, errors.New("EvalList: empty List")
	}

	return nil, nil
}
