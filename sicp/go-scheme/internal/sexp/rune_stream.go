package sexp

import (
	"bufio"
	"bytes"
	"fmt"
	"io"
)

type RuneStream struct {
	in *bufio.Reader
}

func NewRuneStream(in io.Reader) *RuneStream {
	bin := bufio.NewReader(in)
	return &RuneStream{bin}
}

func NewRuneStreamFromBuffer(bs []byte) *RuneStream {
	return NewRuneStream(bytes.NewBuffer(bs))
}

func (s *RuneStream) Next() (rune, error) {
	ch, _, err := s.in.ReadRune()
	if err == nil {
		return ch, nil
	} else {
		if err == io.EOF {
			return 0, err
		} else {
			return 0, fmt.Errorf("Unexpected error: %v", err)
		}
	}
}
