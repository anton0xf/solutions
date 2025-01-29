all: run

run: libhello.so hello
	./hello

libhello.so:
	gcc hello.c --shared -fPIC -o libhello.so

hello: main.c
	gcc main.c -ldl -fPIC -o hello

clean:
	-rm -fv libhello.so hello

test:
# https://github.com/mrtazz/checkmake # use nix
	checkmake Makefile

.PHONY: all test clean
