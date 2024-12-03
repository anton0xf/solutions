# [Advent of Code 2024](https://adventofcode.com/2024) solutions

## Init
Install [scala-cli](https://scala-cli.virtuslab.org/)
```shell
$ scala-cli config power true
$ scala-cli setup-ide .
```
Then open in some editor with BSP support 

## Run
```shell
$ scala-cli run . -M Day03
```

## Test
```shell
$ scala-cli test .
# or with filtering
$ scala-cli test . --test-only 'Day02Test'
$ scala-cli test . --test-only 'Day02Test' -- 'Day02Test.diff'
```