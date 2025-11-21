package sexp

import (
	"fmt"
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestString(t *testing.T) {
	exs := []struct {
		name     string
		expr     Expr
		expected string
	}{
		{"(*Int)(nil)", (*Int)(nil), "<nil>"},
		{"Int{42}", &Int{42}, "42"},
		{"(*Symbol)(nil)", (*Symbol)(nil), "<nil>"},
		{`Symbol{"sym"}`, &Symbol{"sym"}, "sym"},
		{"(*String)(nil)", (*String)(nil), "<nil>"},
		{`String{"qwer"}`, &String{"qwer"}, `"qwer"`},
		{"(*Null)(nil)", (*Null)(nil), "<nil>"},
		{"null", &Null{}, "()"},
		{"(*Pair)(nil)", (*Pair)(nil), "<nil>"},
		{"(cons 1 2)", Cons(&Int{1}, &Int{2}), "(1 . 2)"},
		{"(cons 1 (cons 2 3))",
			Cons(&Int{1}, Cons(&Int{2}, &Int{3})),
			"(1 2 . 3)"},
		{"(cons 1 (cons 2 null))",
			Cons(&Int{1}, Cons(&Int{2}, &Null{})),
			"(1 2)"},
		{"(*Pair)(nil)", (*Pair)(nil), "<nil>"},
		{"(list)", NULL, "()"},
		{"(list (list))", NewList(NULL), "(())"},
		{"(list 1)", NewList(&Int{1}), "(1)"},
		{"(list 1 2)", NewList(&Int{1}, &Int{2}), "(1 2)"},
		{"(list 1 (list 2 3) 4)",
			NewList(&Int{1}, NewList(&Int{2}, &Int{3}), &Int{4}),
			"(1 (2 3) 4)"},
		{"(list (cons 1 2))", NewList(Cons(&Int{1}, &Int{2})), "((1 . 2))"},
		{"(*Quoted)(nil)", (*Quoted)(nil), "<nil>"},
		{"&Quoted{nil}", &Quoted{nil}, "'<nil>"},
		{"(quote sym)", &Quoted{&Symbol{"sym"}}, "'sym"},
	}
	for _, ex := range exs {
		t.Run(ex.name, func(t *testing.T) {
			assert.Equal(t, ex.expected, ex.expr.String())
		})
	}
}

func TestNewList(t *testing.T) {
	assert.Equal(t, NULL, NULL)
	assert.Equal(t, Cons(&Int{1}, NULL), NewList(&Int{1}))
	assert.Equal(t, Cons(&Int{1}, Cons(&Int{2}, NULL)),
		NewList(&Int{1}, &Int{2}))
}

func TestPair_Cons(t *testing.T) {
	assert.Equal(t,
		&Pair{&Int{1}, &String{"a"}},
		Cons(&Int{1}, &String{"a"}))
}

func TestList_Car(t *testing.T) {
	cases := []struct {
		list Expr
		res  Expr
		err  string
	}{
		{nil, nil, "Car: Pair is <nil>"},
		{NULL, nil, "Car: wrong argument type (pair expected): ()"},
		{NewList(&Int{1}), &Int{1}, ""},
		{NewList(&Int{1}, &Int{2}), &Int{1}, ""},
	}
	for _, c := range cases {
		t.Run(fmt.Sprintf("%v", c.list), func(t *testing.T) {
			res, err := Car(c.list)
			if len(c.err) > 0 {
				assert.EqualError(t, err, c.err)
			} else {
				assert.NoError(t, err)
			}
			assert.Equal(t, c.res, res)
		})
	}
}

func TestList_IsList(t *testing.T) {
	examples := []struct {
		expr Expr
		res  bool
	}{
		{&Symbol{"a"}, false},
		{NULL, true},
		{(*Pair)(nil), false},
		{&Pair{nil, &Int{1}}, false},
		{&Pair{&Symbol{"a"}, nil}, false},
		{&Pair{&Symbol{"a"}, &Int{2}}, false},
		{&Pair{&Int{1}, NULL}, true},
		{&Pair{&Int{1}, &Pair{&Int{2}, NULL}}, true},
		{&Pair{&Int{1}, &Pair{&Int{2}, &Int{3}}}, false},
		{&Pair{&Pair{nil, nil}, NULL}, true},
		{NewList(&Int{1}, &Symbol{"a"}), true},
	}
	for _, ex := range examples {
		t.Run(fmt.Sprintf("%s", ex.expr), func(t *testing.T) {
			res := IsList(ex.expr)
			assert.Equal(t, ex.res, res)
		})
	}
}

func TestList_ToArray(t *testing.T) {
	examples := []struct {
		expr Expr
		res  []Expr
		err  string
	}{
		{&Symbol{"a"}, nil, "ToArray: list expected: a"},
		{NULL, nil, ""},
		{(*Pair)(nil), nil, "ToArray: list expected: <nil>"},
		{&Pair{nil, &Int{1}}, nil, "ToArray: list expected: (<nil> . 1)"},
		{&Pair{&Symbol{"a"}, nil}, nil, "ToArray: list expected: (a . <nil>)"},
		{&Pair{&Int{1}, &Int{2}}, nil, "ToArray: list expected: (1 . 2)"},
		{&Pair{&Int{1}, NULL}, []Expr{&Int{1}}, ""},
		{&Pair{&Int{1}, &Pair{&Int{2}, &Int{3}}}, nil, "ToArray: list expected: (1 2 . 3)"},
		{NewList(&Int{1}, &Symbol{"a"}), []Expr{&Int{1}, &Symbol{"a"}}, ""},
		{NewList(&Int{1}, &Int{2}, &Int{3}), []Expr{&Int{1}, &Int{2}, &Int{3}}, ""},
	}
	for _, ex := range examples {
		t.Run(fmt.Sprintf("%s", ex.expr), func(t *testing.T) {
			res, err := ToArray(ex.expr)
			if ex.err == "" {
				assert.NoError(t, err)
			} else {
				assert.EqualError(t, err, ex.err)
			}
			assert.Equal(t, ex.res, res)
		})
	}
}
