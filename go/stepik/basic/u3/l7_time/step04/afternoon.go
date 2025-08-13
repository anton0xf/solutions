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
	dt, err := time.Parse(time.DateTime, strings.TrimSuffix(s, "\n"))
	if err != nil {
		panic(err)
	}
	if dt.Hour() >= 13 {
		dt = dt.AddDate(0, 0, 1)
	}
	fmt.Println(dt.Format(time.DateTime))
}
