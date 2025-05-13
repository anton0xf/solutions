package main

import "fmt"

func main() {
	var s string
	fmt.Scan(&s)
	rs := []rune(s)
	res := make([]rune, 0, len(rs)/2)
	for i := range len(rs) / 2 {
		r := rs[i*2+1]
		res = append(res, r)
	}
	fmt.Println(string(res))
}
