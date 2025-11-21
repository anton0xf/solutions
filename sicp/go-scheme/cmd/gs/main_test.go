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
		{"12 ", "12\n"},
		{"'fф -23", "'fф\n-23\n"},
		{`"1a3"`, "\"1a3\"\n"},
		{"'(1 . (2 . ()))", "'(1 2)\n"},
		{"(inc 1)", "2\n"},
		// TODO uncomment
		// {"(+ 1)", "1\n"},
		// {"(+ 1 2)", "3\n"},
		// {"null", "()"},
		// {"(define a 1) 'a a", "a\n'a\n1\n"},
		// {"(define a 7) a '() (list a 1\n()(2) )", "'a\n7\n()\n(7 1 () (2))\n"},
	}
	for _, c := range cases {
		t.Run(c.in, func(t *testing.T) {
			in := strings.NewReader(c.in)
			out := new(bytes.Buffer)
			err := Run(false, in, out)
			assert.NoError(t, err)
			assert.Equal(t, []byte(c.out), out.Bytes())
		})
	}
}
