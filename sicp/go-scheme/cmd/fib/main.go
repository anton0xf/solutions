package main

import (
	"fmt"
	"go-scheme/internal/fib"
)

func main() {
	fmt.Print("Fibs: ")
	for n := range 10 {
		fmt.Printf("%d ", fib.Fib(n))
	}
	fmt.Println()
}
