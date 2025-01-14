# Hello ZIO

## Init
Install [scala-cli](https://scala-cli.virtuslab.org/)
```shell
$ scala-cli config power true
$ scala-cli setup-ide .
```
Then open in some editor with BSP support

## Run
```shell
$ scala-cli run .
$ scala-cli run . -M HelloZio
```

## Test
```shell
$ scala-cli test .
$ scala-cli test . --test-only 'HelloZioSpec'
$ scala-cli test . --test-only 'HelloZioSpec' -- -t 'run say hello'
```