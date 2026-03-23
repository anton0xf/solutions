package main

import (
	"bytes"
	"strings"
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestRun(t *testing.T) {
	cases := []struct {
		in, out string
	}{
		{"12 ", "12"},
		{"'fф -23", "fф\n-23"},
		{`"1a3"`, "\"1a3\""},
		{`"\u0033 \u2713"`, "\"3 ✓\""},
		{"'(1 . 2)", "(1 . 2)"},
		{"'(1 . (2 . ()))", "(1 2)"},
		{"'()", "()"},
		{"null", "()"},
		{"(inc 1)", "2"},
		{"(inc (+ 1 2))", "4"},
		{"(+)", "0"},
		{"(+ 1)", "1"},
		{"(+ 1 2)", "3"},
		{"(+ 1 2 3)", "6"},
		{"(- 1 2 3)", "-4"},
		{"(*)", "1"},
		{"(* 2)", "2"},
		{"(* 2 4)", "8"},
		{"(* 1 2 3)", "6"},
		{"(/ 70 5 7)", "2"},
		{"(list)", "()"},
		{"(list 1 2)", "(1 2)"},
		{"(cons 1 2)", "(1 . 2)"},
		{"(cons 1 null)", "(1)"},
		{"(cons 1 '(2))", "(1 2)"},
		{"(car '(1 . 2))", "1"},
		{"(car (cons 1 2))", "1"},
		{"(car (list 1 2 3))", "1"},
		{"(cdr (cons 1 2))", "2"},

		// TODO uncomment
		// {"(if #t 1 2)", "1"},
		// {"(define a 1) 'a a", "a\n'a\n1"},
		// {"(define a 7) a '() (list a 1\n()(2) )", "'a\n7\n()\n(7 1 () (2))"},
	}
	for _, c := range cases {
		t.Run(c.in, func(t *testing.T) {
			in := strings.NewReader(c.in)
			out := new(bytes.Buffer)
			err := Run(false, in, out)
			assert.NoError(t, err)
			assert.Equal(t, []byte(c.out+"\n"), out.Bytes())
		})
	}
}
