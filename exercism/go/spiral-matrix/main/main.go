package main

import (
	"os"
	"fmt"
	"strconv"
	"spiralmatrix"
)

// run it by `go run ./main 3` from parent directory
func main() {
	if len(os.Args) < 2 {
		fmt.Fprintf(os.Stderr, "Usage: ./main size\n")
		os.Exit(1)
	}
	size, err := strconv.Atoi(os.Args[1])
	if err != nil {
		fmt.Fprintf(os.Stderr, "parse error: %s\n", err)
		os.Exit(2)
	}
	m := spiralmatrix.SpiralMatrix(size)
	for _, row := range m {
		fmt.Printf("%v\n", row)
	}
}
