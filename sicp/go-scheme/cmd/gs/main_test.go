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
		{"fф -23", "fф\n-23\n"},
		{"12 ", "12\n"},
	}
	for _, c := range cases {
		t.Run(c.in, func(t *testing.T) {
			in := strings.NewReader(c.in)
			out := new(bytes.Buffer)
			err := Run(in, out)
			assert.NoError(t, err)
			assert.Equal(t, []byte(c.out), out.Bytes())
		})
	}
}
