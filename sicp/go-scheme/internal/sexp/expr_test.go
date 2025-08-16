package sexp

import (
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestString(t *testing.T) {
	exs := []struct {
		name     string
		expr     Expr
		expected string
	}{
		{"Int{42}", &Int{42}, "42"},
		{`String{"qwer"}`, &String{"qwer"}, `"qwer"`},
		{`Symbol{"sym"}`, &Symbol{"sym"}, "sym"},
		{"null", &Null{}, "'()"},
		{"(*Pair)(nil)", (*Pair)(nil), "<nil>"},
		{"(cons 1 2)", Cons(&Int{1}, &Int{2}), "'(1 . 2)"},
		// TODO
		// {"(cons 1 (cons 2 . 3))", Cons(&Int{1}, &Int{2}), "'(1 2 . 3)"},
		{"(*List)(nil)", (*List)(nil), "<nil>"},
		{"(list)", NewList(), "'()"},
		{"(list 1)", NewList(&Int{1}), "'(1)"},
		{"(list 1 2)", NewList(&Int{1}, &Int{2}), "'(1 2)"},
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
	assert.Equal(t, &List{nil}, NewList())
	assert.Equal(t, &List{[]Expr{nil}}, NewList(nil))
	assert.Equal(t, &List{[]Expr{&Int{1}}}, NewList(&Int{1}))
}

func TestList_Car(t *testing.T) {
	cases := []struct {
		list *List
		res  Expr
		err  string
	}{
		{nil, nil, "car: list is not initialized"},
		{&List{}, nil, "car: list is empty"},
		{&List{nil}, nil, "car: list is empty"},
		{&List{[]Expr{}}, nil, "car: list is empty"},
		{&List{[]Expr{&Int{1}}}, &Int{1}, ""},
	}
	for _, c := range cases {
		t.Run(c.list.String(), func(t *testing.T) {
			res, err := c.list.Car()
			if len(c.err) > 0 {
				assert.EqualError(t, err, c.err)
			} else {
				assert.NoError(t, err)
			}
			assert.Equal(t, c.res, res)
		})
	}
}
