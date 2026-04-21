package sexp

import (
	"errors"
	"fmt"
	"maps"
	"slices"
	"strings"
)

type Env struct {
	m map[string]Expr
}

type FuncOrForm interface {
	Expr
	GetName() string
}

func (f *Function) GetName() string {
	return f.name
}

func (f *SpecialForm) GetName() string {
	return f.name
}

func NewEnv(vals map[string]Expr, fns []FuncOrForm) *Env {
	m := make(map[string]Expr)
	for k, v := range vals {
		m[k] = v
	}
	for _, fn := range fns {
		if fn == nil {
			panic(errors.New("NewEnv: <nil> function"))
		}
		m[fn.GetName()] = fn
	}
	return &Env{m}
}

func NewEnvDefault() *Env {
	return NewEnv(
		map[string]Expr{
			"null": NULL,
			"#t":   TRUE,
			"#f":   FALSE,
		},
		[]FuncOrForm{
			// special forms
			FQuote,
			// functions
			FnInc, FnDec, FnPlus, FnMinus, FnMult, FnDiv,
			FnList, FnCons, FnCar, FnCdr,
		},
	)
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

func (e *Env) String() string {
	keys := slices.Sorted(maps.Keys(e.m))
	parts := make([]string, len(keys))
	for i, k := range keys {
		parts[i] = fmt.Sprintf("%s: %s", k, e.m[k])
	}
	return "{" + strings.Join(parts, ", ") + "}"
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

	return e.x, nil
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

		switch f := fExpr.(type) {
		case *Function:
			args, err := ToArray(e.y)
			if err != nil {
				return nil, fmt.Errorf("Env.EvalPair: %w", err)
			}

			for i, arg := range args {
				args[i], err = env.Eval(arg)
				if err != nil {
					return nil, fmt.Errorf("Env.EvalPair: %w", err)
				}
			}

			return f.f(args...)

		case *SpecialForm:
			args, err := ToArray(e.y)
			if err != nil {
				return nil, fmt.Errorf("Env.EvalPair: %w", err)
			}

			res, err := f.f(env, args...)
			if err != nil {
				return nil, fmt.Errorf("Env.EvalPair: %w", err)
			}

			return env.Eval(res)

		default:
			return nil, fmt.Errorf(
				"Env.EvalPair: not a special form or function: %s", fExpr)
		}
	}

	return nil, fmt.Errorf("Env.EvalPair: unexpected pair: %s", e)
}
