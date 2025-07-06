package main

// Test:
// $ echo '1 149,6088607594936;1 179,0666666666666' | go run u3/l2/step14/csv_numbers.go
// > 0.9750

import (
	"bufio"
	"fmt"
	"os"
	"strconv"
	"strings"
)

func main() {
	in := bufio.NewReader(os.Stdin)
	line, _ := in.ReadString('\n')
	ns := make([]float64, 2)
	for i, s := range strings.Split(line, ";") {
		s = strings.TrimSpace(s)
		s = strings.ReplaceAll(s, " ", "")
		s = strings.ReplaceAll(s, ",", ".")
		n, _ := strconv.ParseFloat(s, 64)
		ns[i] = n
	}
	fmt.Printf("%.4f\n", ns[0]/ns[1])
}
