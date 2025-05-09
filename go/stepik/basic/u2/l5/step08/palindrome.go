package main

import (
	"bufio"
	"fmt"
	"os"
	"strings"
)

// test it by: $ echo 'топот' | go run u2/l5/step08/palindrome.go
func main() {
	line, _ := bufio.NewReader(os.Stdin).ReadString('\n')
	s := []rune(strings.TrimSpace(line))
	for i := range len(s) / 2 {
		if s[i] != s[len(s)-i-1] {
			fmt.Println("Нет")
			return
		}
	}
	fmt.Println("Палиндром")
}
