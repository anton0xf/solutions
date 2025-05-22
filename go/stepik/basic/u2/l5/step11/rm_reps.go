package main

import "fmt"

func main() {
	var s string
	fmt.Scan(&s)
	rs := []rune(s)

	reps := make(map[rune]int)
	for _, r := range rs {
		reps[r]++
	}

	var res []rune
	for _, r := range rs {
		if reps[r] == 1 {
			res = append(res, r)
		}
	}

	fmt.Println(string(res))
}
