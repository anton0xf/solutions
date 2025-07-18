package main

import (
	"fmt"
	"io"
	"os"

	"go-scheme/internal/sexp"
)

func main() {
	err := Run(os.Stdin, os.Stdout)
	if err != nil {
		panic(err)
	}
}

func Run(in io.Reader, out io.Writer) error {
	parser := sexp.NewParser(in)
	for {
		expr, done, err := parser.Parse()
		if err != nil {
			return err
		}
		if expr != nil {
			// TODO evaluate expr
			fmt.Fprintln(out, expr)
		}
		if done {
			return nil
		}
	}
}
