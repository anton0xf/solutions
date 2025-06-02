# Solutions for some Exercism tracks

## do helper
Call `exercism` cli tool and commit to `git`.

Usage: `./do [global-options] [subcommand args..]`

Subcommands:
* `start  <track> <exercise>` download and commit exercise
* `finish <track> <exercise>` upload and commit solution

Global options:
* `-h`, `--help`    - show help
* `-v`, `--verbose` - verbose mode
* `-n`, `--dry-run` - dry run

Example:
1. copy from exercism something like
```shell
exercism download --track=go --exercise=interest-is-interesting
```
2. use `do` to init task
```shell
./do start go interest-is-interesting
```
3. make it and finish with
```shell
./do finish go interest-is-interesting
```
