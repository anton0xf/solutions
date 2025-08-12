// test: $ echo '1986-04-16T05:20:00+06:00' | go run u3/l7_time/step03/conv.go
package main

import (
	"bufio"
	"fmt"
	"os"
	"strings"
	"time"
)

func main() {
	in := bufio.NewReader(os.Stdin)
	s, err := in.ReadString('\n')
	if err != nil {
		panic(err)
	}

	dt, err := time.Parse(time.RFC3339, strings.TrimSuffix(s, "\n"))
	if err != nil {
		panic(err)
	}

	fmt.Println(dt.Format(time.UnixDate))
}
