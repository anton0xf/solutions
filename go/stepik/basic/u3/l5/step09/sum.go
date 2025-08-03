// Test:
// $ printf '%d\n' 1 2 3 | go run u3/l5/step09/sum.go
// 6
package main

import (
	"bufio"
	"fmt"
	"os"
	"strconv"
)

func main() {
	var sum int64

	sc := bufio.NewScanner(os.Stdin)
	for sc.Scan() {
		s := sc.Text()
		n, err := strconv.ParseInt(s, 10, 64)
		if err != nil {
			panic(fmt.Errorf("parse error: %w", err))
		}
		sum += n
	}
	if err := sc.Err(); err != nil {
		panic(fmt.Errorf("read error: %w", err))
	}

	os.Stdout.WriteString(strconv.FormatInt(sum, 10) + "\n")
}
