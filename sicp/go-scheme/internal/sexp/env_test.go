package sexp

import (
	"fmt"
	"testing"

	"github.com/stretchr/testify/assert"
)

// TODO use gox.Ptr or move to separate file
func Str(s string) *string {
	return &s
}

func TestEnv_Eval(t *testing.T) {
	defaultEnv := NewEnvDefault()

	examples := []struct {
		env      *Env // TODO: make map of envs and pass here only name
		expr     Expr
		envAfter *Env
		result   Expr
		err      string
	}{
		// literals are self-contained
		{&Env{}, &Int{7}, &Env{}, &Int{7}, ""},
		{&Env{}, &String{"aa"}, &Env{}, &String{"aa"}, ""},

		// Quoted
		{&Env{}, (*Quoted)(nil), &Env{}, nil, "Env.EvalQuoted: nil parameter"},
		{&Env{}, &Quoted{nil}, &Env{}, nil, "Env.EvalQuoted: Quoted{nil}"},
		// quoted literal is just literal
		{&Env{}, &Quoted{&Int{3}}, &Env{}, &Int{3}, ""},
		{&Env{}, &Quoted{&String{"aa"}}, &Env{}, &String{"aa"}, ""},
		// other quotations don't change
		{&Env{}, &Quoted{&Symbol{"x"}}, &Env{}, &Quoted{&Symbol{"x"}}, ""},
		{&Env{}, &Quoted{NewList(&Int{1})},
			&Env{}, &Quoted{NewList(&Int{1})}, ""},

		// Symbol
		{&Env{}, (*Symbol)(nil), &Env{}, nil, "Env.EvalSymbol: nil parameter"},
		{&Env{}, &Symbol{""}, &Env{}, nil, "Env.Get: empty symbol name"},
		{&Env{}, &Symbol{"x"}, &Env{}, nil, "Env.Get: symbol 'x not defined"},
		{&Env{map[string]Expr{"x": &Int{4}}},
			&Symbol{"x"},
			&Env{map[string]Expr{"x": &Int{4}}},
			&Int{4}, ""},

		// List
		{&Env{}, NULL, &Env{}, nil, "Env.Eval: empty list"},
		{&Env{}, (*Pair)(nil), &Env{}, nil, "Env.EvalPair: nil parameter"},
		{&Env{}, &Pair{nil, nil}, &Env{}, nil, "Env.EvalPair: nil head"},

		// call function
		{&Env{}, NewList(&Symbol{"a"}), &Env{}, nil,
			"Env.EvalPair: Env.Get: symbol 'a not defined"},
		{&Env{map[string]Expr{"a": &Int{1}}},
			NewList(&Symbol{"a"}),
			&Env{map[string]Expr{"a": &Int{1}}},
			nil, "Env.EvalPair: not a function: 1"},
		{defaultEnv, NewListWithTail([]Expr{&Symbol{"inc"}}, nil), defaultEnv, nil,
			"Env.EvalPair: ToArray: unsupported type: <nil>"},
		{defaultEnv, NewList(&Symbol{"inc"}, &Int{1}), defaultEnv, &Int{2}, ""},
		{defaultEnv, NewList(&Symbol{"inc"}, &Symbol{"a"}), defaultEnv, nil,
			"Env.EvalPair: Env.Get: symbol 'a not defined"},
		{defaultEnv, NewList(&Symbol{"inc"}, NewList(&Symbol{"inc"}, &Int{1})),
			defaultEnv, &Int{3}, ""},

		// special forms

		// TODO define
	}
	for _, ex := range examples {
		// TODO make env printing more readable
		t.Run(fmt.Sprintf("[%v] %v", ex.env, ex.expr), func(t *testing.T) {
			res, err := ex.env.Eval(ex.expr)
			if len(ex.err) > 0 {
				assert.EqualError(t, err, ex.err)
			} else {
				assert.NoError(t, err)
			}
			assert.Equal(t, ex.result, res)
			assert.Equal(t, ex.envAfter, ex.env)
		})
	}
}
