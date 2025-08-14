// test: $ echo '13.03.2018 14:00:15,12.03.2018 14:00:15' | go run u3/l7_time/step07/duration.go
package main

import (
	"bufio"
	"fmt"
	"io"
	"os"
	"strings"
	"time"
)

func main() {
	in := bufio.NewReader(os.Stdin)
	line, err := in.ReadString('\n')
	if err != nil && err != io.EOF {
		panic(err)
	}
	strs := strings.Split(strings.TrimRight(line, "\n"), ",")
	if len(strs) != 2 {
		panic(fmt.Errorf("expected 2 dates: %v", strs))
	}
	dts := make([]time.Time, 2)
	for i, s := range strs {
		dts[i], err = time.Parse("02.01.2006 15:04:05", s)
		if err != nil {
			panic(err)
		}
	}
	if dts[1].After(dts[0]) {
		fmt.Println(dts[1].Sub(dts[0]))
	} else {
		fmt.Println(dts[0].Sub(dts[1]))
	}
}
