// run by: $ go run u3/l5/step14/search_zero.go
package main

import (
	"bufio"
	"fmt"
	"os"
)

func main() {
	file, err := os.Open("test/data/task.data")
	if err != nil {
		panic(err)
	}
	defer func() {
		err := file.Close()
		if err != nil {
			panic(err)
		}
	}()

	r := bufio.NewReader(file)
	for i := 1; ; i++ {
		s, err := r.ReadString(';')
		if err != nil {
			panic(err)
		}

		if s == "0;" {
			fmt.Println(i)
			return
		}
	}
}
