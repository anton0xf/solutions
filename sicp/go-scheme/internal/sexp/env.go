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

	case *Pair:
		return env.EvalPair(e)

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

func (env *Env) EvalPair(e *Pair) (Expr, error) {
	if e == nil {
		return nil, errors.New("Env.EvalPair: nil parameter")
	}

	if e.x == nil {
		return nil, errors.New("Env.EvalPair: nil head")
	}

	switch head := e.x.(type) {
	case *Symbol:
		fExpr, err := env.Get(head.name)
		if err != nil {
			return nil, fmt.Errorf("Env.EvalPair: %w", err)
		}

		f, fOk := fExpr.(*Function)
		if !fOk {
			return nil, fmt.Errorf("Env.EvalPair: not a function: %s", fExpr)
		}

		args, err := ToArray(e.y)
		if err != nil {
			return nil, fmt.Errorf("Env.EvalPair: %w", err)
		}

		return f.f(args...)
	}

	return nil, fmt.Errorf("Env.EvalPair: unexpected pair: %s", e)
}
