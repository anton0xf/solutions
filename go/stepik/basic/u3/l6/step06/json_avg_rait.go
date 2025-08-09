// test: $ go run u3/l6/step06/json_avg_rait.go <test/data/u3_l6_step06.data.json
package main

import (
	"encoding/json"
	"os"
)

type Student struct {
	Rating []int
}

type Group struct {
	Students []Student
}

type Result struct {
	Average float64
}

func main() {
	group := &Group{}
	dec := json.NewDecoder(os.Stdin)
	err := dec.Decode(group)
	if err != nil {
		panic(err)
	}

	count := len(group.Students)
	sum := 0
	for _, student := range group.Students {
		sum += len(student.Rating)
	}

	result := &Result{
		Average: float64(sum) / float64(count),
	}
	enc := json.NewEncoder(os.Stdout)
	enc.SetIndent("", "    ")
	err = enc.Encode(result)
	if err != nil {
		panic(err)
	}
}
