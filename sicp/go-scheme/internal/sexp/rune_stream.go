package sexp

import (
	"bufio"
	"fmt"
	"io"
)

type RuneStream struct {
	in *bufio.Reader
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
