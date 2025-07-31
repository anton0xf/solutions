package sexp

import (
	"testing"

	"github.com/stretchr/testify/assert"
)

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
		res, err := c.list.Car()
		assert.Equal(t, c.res, res)
		if len(c.err) > 0 {
			assert.EqualError(t, err, c.err)
		}
	}
}
