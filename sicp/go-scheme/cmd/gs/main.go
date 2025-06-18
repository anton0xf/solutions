package main

import (
	"fmt"
	"os"

	"go-scheme/internal/sexp"
)

func main() {
	parser := sexp.NewParser(os.Stdin)
	for {
		expr, done, err := parser.Parse()
		if err != nil {
			panic(err)
		}
		if done {
			fmt.Println()
			return
		}
		// TODO evaluate expr
		fmt.Print(expr)
	}
}
