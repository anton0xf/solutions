# HowTo
[scala-cli](https://scala-cli.virtuslab.org/) project. See `./project.scala`

```shell
# print used versions
$ scala-cli version
Scala CLI version: 1.4.1
Scala version (default): 3.4.2

# prepare idea/metals project
$ scala-cli setup-ide .

# run all (https://scala-cli.virtuslab.org/docs/commands/run)
$ scala-cli run .
# or just one main
$ scala-cli run . --main-class hello

# test all (https://scala-cli.virtuslab.org/docs/commands/test)
$ scala-cli test .
# or with filtering
$ scala-cli test . --test-only 'MyTests' -- 'MyTests.test'
```

# Languages
## [Arith] Untyped Arithmetic Expression
```bnf
t ::=                           terms:
    true                        constant true
    false                       constant false
    if t then t else t          conditional
    0                           constant zero
    succ t                      successor
    pred t                      predecessor
    iszero t                    zero test
    (t)                         brackets
```