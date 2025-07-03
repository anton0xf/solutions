package main

import (
	"bytes"
	"strings"
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestRun(t *testing.T) {
	t.Run("echo", func(t *testing.T) {
		in := strings.NewReader("fф -23")
		out := new(bytes.Buffer)
		err := Run(in, out)
		assert.NoError(t, err)
		assert.Equal(t, []byte("fф\n-23\n"), out.Bytes())
	})

	t.Run("echo with trailing spaces", func(t *testing.T) {
		in := strings.NewReader("12 ")
		out := new(bytes.Buffer)
		err := Run(in, out)
		assert.NoError(t, err)
		assert.Equal(t, []byte("12\n"), out.Bytes())
	})
}
