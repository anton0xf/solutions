all: run

run: hello
	./hello

hello: main.c
	gcc -o hello main.c

clean:
	-rm -fv hello

test:
# https://github.com/mrtazz/checkmake # use nix or brew
	checkmake Makefile

.PHONY: all test clean
