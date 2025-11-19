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
	examples := []struct {
		env      *Env
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
		{&Env{}, (*List)(nil), &Env{}, nil, "Env.EvalList: nil parameter"},
		{&Env{}, &List{nil}, &Env{}, nil, "Env.EvalList: List{nil}"},
		{&Env{}, (*Pair)(nil), &Env{}, nil, "Env.EvalPair: nil parameter"},
		{&Env{}, &Pair{nil, nil}, &Env{}, nil, "Env.EvalPair: nil head"},
		{&Env{}, NewList(), &Env{}, nil, "Env.Eval: empty list"},
		// TODO call function

		// special forms

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
