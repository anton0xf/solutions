# Go Scheme
Simple Scheme-like languages demonstrating different evaluation strategies and so on.

## Run
Run command `fib`
```shell
$ go run ./cmd/fib
```

## Unit tests
Run all tests:
```shell
$ go test ./...
```

## Test app
```shell
$ echo '"asdф ☺️"' | go run ./cmd/gs
"asdф☺️"
```
Or in interactive mode:
```shell
$ rlwrap go run ./cmd/gs
```
```lisp
> "\u0033\t\u2713\t\U0001f600"
"3      ✓       😀"
> (+ (inc (* 3 4)) 5 (- 3 7) -6)
8
> (/ 70 5 7)
2
> '((a . b) . (c . (d . (e . ()))))
'((a . b) c d e)
>
```
