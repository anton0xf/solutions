package main

import (
	"fmt"
	"io"
	"os"

	"github.com/mattn/go-isatty"

	"go-scheme/internal/sexp"
)

func main() {
	interactive := isatty.IsTerminal(os.Stdin.Fd())
	err := Run(interactive, os.Stdin, os.Stdout)
	if err != nil {
		panic(err)
	}
}

func Run(interactive bool, in io.Reader, out io.Writer) error {
	parser := sexp.NewParser(in)
	env := &sexp.Env{}
	for {
		if interactive {
			fmt.Fprint(out, "> ")
		}
		expr, done, err := parser.Parse()
		if err != nil {
			return err
		}
		if expr != nil {
			res, err := env.Eval(expr)
			if err != nil {
				fmt.Fprintf(out, "error: %s\n", err)
			} else {
				fmt.Fprintln(out, res)
			}
		}
		if done {
			return nil
		}
	}
}
