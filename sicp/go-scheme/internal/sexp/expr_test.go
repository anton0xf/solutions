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
		{"(*List)(nil)", (*List)(nil), "<nil>"},
		{"(list)", NewList(), "()"},
		{"(list (list))", NewList(NewList()), "(())"},
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
	assert.Equal(t, NULL, NewList())
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
		{NewList(), nil, "Car: wrong argument type (pair expected): ()"},
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
