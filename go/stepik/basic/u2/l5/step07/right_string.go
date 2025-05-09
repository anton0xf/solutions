package main

import (
	"bufio"
	"fmt"
	"os"
	"strings"
	"unicode"
)

// Test with: $ echo 'Привет.' | go run u2/l5/step07/right_string.go
func main() {
	text, _ := bufio.NewReader(os.Stdin).ReadString('\n')
	cs := []rune(strings.TrimSpace(text))
	first := cs[0]
	last := cs[len(cs)-1]
	if unicode.IsUpper(first) && last == '.' {
		fmt.Println("Right")
	} else {
		fmt.Println("Wrong")
	}
}
