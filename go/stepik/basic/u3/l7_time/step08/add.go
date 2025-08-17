// test: $ echo '12 мин. 13 сек.' | go run u3/l7_time/step08/add.go
package main

import (
	"fmt"
	"time"
)

// вам это понадобится
const now = 1589570165

func main() {
	var m, s int
	var m_sym, s_sym string
	_, err := fmt.Scan(&m, &m_sym, &s, &s_sym)
	if err != nil {
		panic(err)
	}

	p := time.Duration(m)*time.Minute + time.Duration(s)*time.Second
	dt := time.Unix(now, 0).UTC()
	fmt.Println(dt.Add(p).Format(time.UnixDate))
}
