# Programming for Linux course
some solutions for https://stepik.org/548

## lecture notes
https://github.com/BorisDeLaMar/LinuxBasicsForked

## docker image for testing
about: https://stepik.org/lesson/26302/step/7?unit=8180
image page: https://hub.docker.com/r/osll/mooc_linux_programming/

run it with
```shell
$ docker pull osll/mooc_linux_programming
$ ﻿docker run -it osll/mooc_linux_programming /bin/bash﻿
```

to test examples in Docker mount this directory to `/app` and work there
```shell
$ docker run -it -v '.:/app' -w /app osll/mooc_linux_programming /bin/bash
root@4b7d9f90a62b:/app# cd u1/l1/hello/
root@4b7d9f90a62b:/app/u1/l1/hello# make run
gcc -o hello main.c
./hello
Hello!
```

## useful tools
### utils
* nm - list symbols from object files
* ldd - print shared object dependencies

### linters
https://github.com/mrtazz/checkmake
```shell
$ nix-env -i checkmake
```
