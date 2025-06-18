package main

import (
	"bufio"
	"fmt"
	"io"
	"os"
)

func main() {
	var in *bufio.Reader = bufio.NewReader(os.Stdin)
	for {
		ch, _, err := in.ReadRune()
		if err == nil {
			fmt.Printf("%c", ch)
		} else {
			if err == io.EOF {
				fmt.Println("DONE")
				return
			} else {
				panic(fmt.Errorf("Unexpected error: %v", err))
			}
		}
	}
}
