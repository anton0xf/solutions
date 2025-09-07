package main

import (
	"fmt" // пакет используется для проверки выполнения условия задачи, не удаляйте его
	"sync"
	"time" // пакет используется для проверки выполнения условия задачи, не удаляйте его
)

const N = 5

func main() {
	fn := func(x int) int {
		time.Sleep(N * time.Second)
		return x * 3
	}
	in1 := make(chan int)
	in2 := make(chan int)
	out := make(chan int)

	start := time.Now()
	merge2Channels(fn, in1, in2, out, N)

	for i := range N {
		in1 <- i
		in2 <- i + 100
	}

	for i := range N {
		expected := (i*2 + 100) * 3
		y := <-out
		if y != expected {
			fmt.Printf("unexpected res at i=%d: %d. expected: %d\n", i, y, expected)
		}
	}
	duration := time.Since(start)
	if duration.Seconds() > N+1 {
		fmt.Println("Время превышено")
	}
	fmt.Println("Время выполнения: ", duration)
}

func merge2Channels(fn func(int) int, in1 <-chan int, in2 <-chan int, out chan<- int, n int) {
	wg := new(sync.WaitGroup)

	applyFn := func(in <-chan int, out []int, id int) {
		for i := range n {
			x := <-in
			go func(i int) {
				out[i] = fn(x)
				wg.Done()
			}(i)
		}
	}

	res1, res2 := make([]int, n), make([]int, n)
	wg.Add(2 * n)
	go applyFn(in1, res1, 1)
	go applyFn(in2, res2, 2)
	go func() {
		wg.Wait()

		for i := range n {
			y1 := res1[i]
			y2 := res2[i]
			out <- y1 + y2
		}
	}()
}
