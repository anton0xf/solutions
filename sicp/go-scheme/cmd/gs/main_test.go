package main

import (
	"bytes"
	"strings"
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestRun(t *testing.T) {
	t.Run("echo", func(t *testing.T) {
		in := strings.NewReader("fф")
		out := new(bytes.Buffer)
		err := Run(in, out)
		assert.NoError(t, err)
		assert.Equal(t, []byte("fф\n"), out.Bytes())
	})
}
