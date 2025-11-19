package sexp

import (
	"errors"
	"fmt"
)

type Env struct {
	m map[string]Expr
}

func (env *Env) Get(name string) (Expr, error) {
	if name == "" {
		return nil, errors.New("Env.Get: empty symbol name")
	}
	expr, ok := env.m[name]
	if ok {
		return expr, nil
	} else {
		return nil, fmt.Errorf("Env.Get: symbol '%s not defined", name)
	}
}

func (env *Env) Eval(expr Expr) (Expr, error) {
	switch e := expr.(type) {
	case *Int, *String:
		return e, nil

	case *Symbol:
		return env.EvalSymbol(e)

	case *Quoted:
		return EvalQuoted(e)

	case *Null:
		return nil, errors.New("Env.Eval: empty list")

	case *List:
		return EvalList(e)

	default:
		return nil, fmt.Errorf(
			"Env.Eval: unexpected type %T of parameter %v", expr, expr)
	}
}

func (env *Env) EvalSymbol(e *Symbol) (Expr, error) {
	if e == nil {
		return nil, errors.New("Env.EvalSymbol: nil parameter")
	}

	return env.Get(e.name)
}

func EvalQuoted(e *Quoted) (Expr, error) {
	if e == nil {
		return nil, errors.New("Env.EvalQuoted: nil parameter")
	}

	if e.x == nil {
		return nil, errors.New("Env.EvalQuoted: Quoted{nil}")
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
		return nil, errors.New("Env.EvalList: nil parameter")
	}

	if len(e.xs) == 0 {
		return nil, errors.New("Env.EvalList: List{nil}")
	}

	return nil, nil
}
