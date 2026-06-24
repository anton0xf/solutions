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

// env key-value pair
type ekv struct {
	key string
	val Expr
}

func env(kvs ...ekv) *Env {
	m := make(map[string]Expr)
	for _, kv := range kvs {
		m[kv.key] = kv.val
	}
	return &Env{m}
}

func envIsEmpty(t *testing.T, actualEnv *Env) {
	assert.Empty(t, actualEnv.m)
}

func envIsEqual(expectedEnv *Env) func(t *testing.T, actualEnv *Env) {
	return func(t *testing.T, actualEnv *Env) {
		assert.Equal(t, actualEnv, expectedEnv)
	}
}

func checkEvalRes(
	t *testing.T,
	env *Env,
	expr Expr,
	result Expr,
	checkEnv func(t *testing.T, env *Env),
) {
	t.Run(fmt.Sprintf("%v", expr), func(t *testing.T) {
		res, err := env.Eval(expr)
		assert.NoError(t, err)
		assert.Equal(t, result, res)
		checkEnv(t, env)
	})
}

func checkEvalErr(
	t *testing.T,
	env *Env,
	expr Expr,
	errStr string,
	checkEnv func(t *testing.T, env *Env),
) {
	t.Run(fmt.Sprintf("%v", expr), func(t *testing.T) {
		res, err := env.Eval(expr)
		assert.EqualError(t, err, errStr)
		assert.Nil(t, res)
		checkEnv(t, env)
	})
}

func TestEnv_Eval(t *testing.T) {
	// check ok with empty env
	okE := func(expr Expr, res Expr) {
		checkEvalRes(t, env(), expr, res, envIsEmpty)
	}
	// check err with empty env
	errE := func(expr Expr, err string) {
		checkEvalErr(t, env(), expr, err, envIsEmpty)
	}
	// check ok with unchanged env
	okU := func(env *Env, expr Expr, res Expr) {
		copy := env.Clone()
		checkEvalRes(t, env, expr, res, envIsEqual(copy))
	}
	// check err with unchanged env
	errU := func(env *Env, expr Expr, err string) {
		copy := env.Clone()
		checkEvalErr(t, env, expr, err, envIsEqual(copy))
	}

	defEnv := func(kvs ...ekv) *Env {
		e := NewEnvDefault()
		for _, kv := range kvs {
			e.m[kv.key] = kv.val
		}
		return e
	}

	// check ok with changed env
	// ok := func(env *Env, expr Expr, res Expr, expectedEnv *Env) {
	// 	checkEvalRes(t, env, expr, res, envIsEqual(expectedEnv))
	// }

	// literals are self-contained
	okE(&Int{7}, &Int{7})
	okE(&String{"aa"}, &String{"aa"})

	// Quoted
	errE((*Quoted)(nil), "Env.EvalQuoted: nil parameter")
	errE(&Quoted{nil}, "Env.EvalQuoted: Quoted{nil}")
	okE(&Quoted{&Int{3}}, &Int{3})
	okE(&Quoted{&String{"aa"}}, &String{"aa"})
	okE(&Quoted{&Symbol{"x"}}, &Symbol{"x"})
	okE(&Quoted{NewList(&Int{1})}, NewList(&Int{1}))

	// Symbol
	errE((*Symbol)(nil), "Env.EvalSymbol: nil parameter")
	errE(&Symbol{""}, "Env.Get: empty symbol name")
	errE(&Symbol{"x"}, "Env.Get: symbol 'x not defined")
	okU(env(ekv{"x", &Int{4}}), &Symbol{"x"}, &Int{4})

	// List
	errE(NULL, "Env.Eval: empty list")
	errE((*Pair)(nil), "Env.EvalPair: nil parameter")
	errE(&Pair{nil, nil}, "Env.EvalPair: nil head")

	// call function
	errE(NewList(&Symbol{"a"}), "Env.EvalPair: Env.Get: symbol 'a not defined")
	errU(env(ekv{"a", &Int{1}}), NewList(&Symbol{"a"}),
		"Env.EvalPair: not a special form or function: 1")
	errU(defEnv(), NewListWithTail([]Expr{&Symbol{"inc"}}, nil),
		"Env.EvalPair: ToArray: list expected: <nil>")
	okU(defEnv(), NewList(&Symbol{"inc"}, &Int{1}), &Int{2})
	errU(defEnv(), NewList(&Symbol{"inc"}, &Symbol{"a"}),
		"Env.EvalPair: Env.Get: symbol 'a not defined")
	okU(defEnv(), NewList(&Symbol{"inc"}, NewList(&Symbol{"inc"}, &Int{1})),
		&Int{3})

	// special forms
	okU(defEnv(), NewList(&Symbol{"quote"}, &Int{1}), &Int{1})
	okU(defEnv(), NewList(&Symbol{"quote"}, &Symbol{"a"}), &Symbol{"a"})
	errU(defEnv(), NewList(&Symbol{"quote"}, &Int{1}, &Symbol{"a"}),
		"quote: unexpected number of arguments")

	// if - true branch
	okU(defEnv(), NewList(&Symbol{"if"}, TRUE, &Int{1}, &Int{2}),
		&Int{1})
	okU(defEnv(), NewList(&Symbol{"if"}, FALSE, &Int{1}, &Int{2}),
		&Int{2})
	okU(defEnv(), NewList(&Symbol{"if"}, TRUE, &Int{1}),
		&Int{1})
	okU(defEnv(), NewList(&Symbol{"if"}, FALSE, &Int{1}), FALSE)
	okU(defEnv(), NewList(&Symbol{"if"}, &Int{5}, &Int{1}, &Int{2}),
		&Int{1})
	okU(defEnv(), NewList(&Symbol{"if"}, &String{"test"}, &Int{1}, &Int{2}),
		&Int{1})
	okU(defEnv(), NewList(&Symbol{"if"}, &Quoted{NULL}, &Int{1}, &Int{2}),
		&Int{1})
	errU(defEnv(), NewList(&Symbol{"if"}, NULL, &Int{1}, &Int{2}),
		"Env.Eval: empty list")
	okU(defEnv(), NewList(&Symbol{"if"}, TRUE,
		NewList(&Symbol{"+"}, &Int{1}, &Int{2}), &Int{99}), &Int{3})
	okU(defEnv(), NewList(&Symbol{"if"}, FALSE, &Int{99},
		NewList(&Symbol{"+"}, &Int{10}, &Int{20})), &Int{30})
	errU(defEnv(), NewList(&Symbol{"if"}),
		"if: unexpected number of arguments (expected 2 or 3)")
	errU(defEnv(), NewList(&Symbol{"if"}, TRUE),
		"if: unexpected number of arguments (expected 2 or 3)")

	// and - short-circuit evaluation
	okU(defEnv(), NewList(&Symbol{"and"}), TRUE)
	errU(defEnv(), NewList(&Symbol{"and"}, NULL), "Env.Eval: empty list")
	okU(defEnv(), NewList(&Symbol{"and"}, &Int{1}), &Int{1})
	okU(defEnv(), NewList(&Symbol{"and"}, &Int{1}, &Int{2}), &Int{2})
	okU(defEnv(), NewList(&Symbol{"and"}, FALSE, &Int{1}), FALSE)
	okU(defEnv(), NewList(&Symbol{"and"}, &Int{1}, FALSE, &Int{2}), FALSE)
	okU(defEnv(), NewList(&Symbol{"and"}, &Int{1}, &Int{2}, &Int{3}), &Int{3})
	okU(defEnv(), NewList(&Symbol{"and"}, TRUE, FALSE), FALSE)

	// or - short-circuit evaluation
	okU(defEnv(), NewList(&Symbol{"or"}), FALSE)
	errU(defEnv(), NewList(&Symbol{"or"}, NULL), "Env.Eval: empty list")
	okU(defEnv(), NewList(&Symbol{"or"}, &Int{1}), &Int{1})
	okU(defEnv(), NewList(&Symbol{"or"}, &Int{1}, &Int{2}), &Int{1})
	okU(defEnv(), NewList(&Symbol{"or"}, FALSE, &Int{1}), &Int{1})
	okU(defEnv(), NewList(&Symbol{"or"}, FALSE, FALSE, &Int{1}), &Int{1})
	okU(defEnv(), NewList(&Symbol{"or"}, FALSE, FALSE), FALSE)
	okU(defEnv(), NewList(&Symbol{"or"}, TRUE, &Int{1}), TRUE)

	// numbers (in)equality
	okU(defEnv(), NewList(&Symbol{"<"}, &Int{0}, &Int{1}), TRUE)

	// TODO define
	// {defEnv(), NewList(&Symbol{"define"}, &Symbol{"foo"}, &Int{1}),
	// 	defEnv.With("foo", &Int{1}), &Symbol{"foo"}, ""},
}
