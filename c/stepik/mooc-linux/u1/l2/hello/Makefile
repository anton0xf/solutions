all: run

run: libhello.so hello
	LD_LIBRARY_PATH=. ./hello

libhello.so:
	gcc -o libhello.so --shared -fPIC hello.c

hello: main.c hello.h
	gcc main.c -fPIC -L. -lhello -o hello

clean:
	-rm -fv libhello.so hello

test:
# https://github.com/mrtazz/checkmake # use nix
	checkmake Makefile

.PHONY: all test clean
