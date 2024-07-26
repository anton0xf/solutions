## HowTo
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