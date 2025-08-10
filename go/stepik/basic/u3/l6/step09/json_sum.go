// run: $ go run u3/l6/step09/json_sum.go
package main

import (
	"bufio"
	"encoding/json"
	"fmt"
	"os"
)

type Item struct {
	GlobalId int64 `json:"global_id"`
}

func main() {
	file, err := os.Open("test/data/u3_l6_step09_json/data-20190514T0100.json")
	if err != nil {
		panic(err)
	}
	defer func() {
		err := file.Close()
		if err != nil {
			panic(err)
		}
	}()

	var items []Item
	in := bufio.NewReader(file)
	dec := json.NewDecoder(in)
	err = dec.Decode(&items)
	if err != nil {
		panic(err)
	}

	var sum int64 = 0
	for _, item := range items {
		sum += item.GlobalId
	}
	fmt.Println(sum)
}
