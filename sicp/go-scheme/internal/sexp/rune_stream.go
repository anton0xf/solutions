package sexp

import (
	"bufio"
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

func (s *RuneStream) Next() (next rune, eof bool, err error) {
	ch, _, err := s.in.ReadRune()
	if err == nil {
		return ch, false, nil
	} else {
		if err == io.EOF {
			return 0, true, nil
		} else {
			return 0, false, fmt.Errorf("Unexpected error: %v", err)
		}
	}
}

func (s *RuneStream) UnreadRune() error {
	return s.in.UnreadRune()
}
