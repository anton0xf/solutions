# [Функциональная Scala 3 для начинающих программистов](https://stepik.org/course/195883)

## HowTo
[scala-cli](https://scala-cli.virtuslab.org/) project. See `./project.scala`

```shell
# prepare idea/metals project
$ scala-cli config power true
$ scala-cli setup-ide .

# run all (https://scala-cli.virtuslab.org/docs/commands/run)
$ scala-cli run .
# or just one main
$ scala-cli run . --main-class hello

# test all (https://scala-cli.virtuslab.org/docs/commands/test)
$ scala-cli test .
# or with filtering
$ scala-cli test . --test-only 'TestExample' -- 'TestExample.test'
```
