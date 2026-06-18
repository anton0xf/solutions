package sexp

import (
	"fmt"
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestFunction(t *testing.T) {
	for _, ex := range []struct {
		fn   *Function
		args []Expr
		res  Expr
		err  string
	}{
		{FnLt, nil, nil, "<: expected at least 2 arguments"},
		{FnLt, []Expr{&Int{1}}, nil, "<: expected at least 2 arguments"},
		{FnLt, []Expr{&String{"err"}, &Int{1}}, nil, "<: unexpected argument type: [0] \"err\""},
		{FnLt, []Expr{(*Int)(nil), &Int{1}}, nil, "<: nil argument 0"},
		{FnLt, []Expr{&Int{0}, &Int{1}}, TRUE, ""},
		{FnLt, []Expr{&Int{0}, &Int{0}}, FALSE, ""},
		{FnLt, []Expr{&Int{0}, &Int{1}, &Int{-1}}, FALSE, ""},
		{FnLt, []Expr{&Int{0}, &Int{1}, &Int{2}}, TRUE, ""},
	} {
		t.Run(fmt.Sprintf("%s(%v)", ex.fn.name, ex.args), func(t *testing.T) {
			res, err := ex.fn.f(ex.args...)
			if len(ex.err) > 0 {
				assert.EqualError(t, err, ex.err)
			} else {
				assert.NoError(t, err)
			}
			assert.Equal(t, ex.res, res)
		})
	}
}
