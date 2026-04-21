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
		{&Env{}, &Quoted{&Int{3}}, &Env{}, &Int{3}, ""},
		{&Env{}, &Quoted{&String{"aa"}}, &Env{}, &String{"aa"}, ""},
		{&Env{}, &Quoted{&Symbol{"x"}}, &Env{}, &Symbol{"x"}, ""},
		{&Env{}, &Quoted{NewList(&Int{1})}, &Env{}, NewList(&Int{1}), ""},

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
			nil, "Env.EvalPair: not a special form or function: 1"},
		{defaultEnv, NewListWithTail([]Expr{&Symbol{"inc"}}, nil), defaultEnv, nil,
			"Env.EvalPair: ToArray: list expected: <nil>"},
		{defaultEnv, NewList(&Symbol{"inc"}, &Int{1}), defaultEnv, &Int{2}, ""},
		{defaultEnv, NewList(&Symbol{"inc"}, &Symbol{"a"}), defaultEnv, nil,
			"Env.EvalPair: Env.Get: symbol 'a not defined"},
		{defaultEnv, NewList(&Symbol{"inc"}, NewList(&Symbol{"inc"}, &Int{1})),
			defaultEnv, &Int{3}, ""},

		// special forms
		{defaultEnv, NewList(&Symbol{"quote"}, &Int{1}), defaultEnv, &Int{1}, ""},
		{defaultEnv, NewList(&Symbol{"quote"}, &Symbol{"a"}), defaultEnv,
			&Symbol{"a"}, ""},
		{defaultEnv, NewList(&Symbol{"quote"}, &Int{1}, &Symbol{"a"}), defaultEnv,
			nil, "quote: unexpected number of arguments"},

		// if - true branch
		{defaultEnv, NewList(&Symbol{"if"}, TRUE, &Int{1}, &Int{2}), defaultEnv, &Int{1}, ""},
		{defaultEnv, NewList(&Symbol{"if"}, FALSE, &Int{1}, &Int{2}), defaultEnv, &Int{2}, ""},
		{defaultEnv, NewList(&Symbol{"if"}, TRUE, &Int{1}), defaultEnv, &Int{1}, ""},
		{defaultEnv, NewList(&Symbol{"if"}, FALSE, &Int{1}), defaultEnv, FALSE, ""},
		{defaultEnv, NewList(&Symbol{"if"}, &Int{5}, &Int{1}, &Int{2}), defaultEnv, &Int{1}, ""},
		{defaultEnv, NewList(&Symbol{"if"}, &String{"test"}, &Int{1}, &Int{2}), defaultEnv, &Int{1}, ""},
		{defaultEnv, NewList(&Symbol{"if"}, &Quoted{NULL}, &Int{1}, &Int{2}), defaultEnv, &Int{1}, ""},
		{defaultEnv, NewList(&Symbol{"if"}, NULL, &Int{1}, &Int{2}), defaultEnv, nil,
			"Env.Eval: empty list"},
		{defaultEnv, NewList(&Symbol{"if"}, TRUE, NewList(&Symbol{"+"}, &Int{1}, &Int{2}), &Int{99}),
			defaultEnv, &Int{3}, ""},
		{defaultEnv, NewList(&Symbol{"if"}, FALSE, &Int{99}, NewList(&Symbol{"+"}, &Int{10}, &Int{20})),
			defaultEnv, &Int{30}, ""},
		{defaultEnv, NewList(&Symbol{"if"}), defaultEnv, nil,
			"if: unexpected number of arguments (expected 2 or 3)"},
		{defaultEnv, NewList(&Symbol{"if"}, TRUE), defaultEnv, nil,
			"if: unexpected number of arguments (expected 2 or 3)"},

		// TODO define
	}
	for _, ex := range examples {
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
