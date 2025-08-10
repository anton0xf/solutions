package sexp

import "errors"

type Env struct{}

func (env *Env) Eval(expr Expr) (Expr, error) {
	switch e := expr.(type) {
	case *Quoted:
		return EvalQuoted(e)

	case *List:
		return EvalList(e)

	default:
		return e, nil
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
	// if e == nil {
	return nil, nil
}
