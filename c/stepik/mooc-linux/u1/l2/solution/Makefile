all: run

run: lib/libsolution.so main
	LD_LIBRARY_PATH=lib ./main

lib/libsolution.so:
	gcc -o lib/libsolution.so --shared -fPIC lib/solution.c

main: main.c
	gcc main.c -fPIC -Llib -lsolution -o main

clean:
	-rm -fv lib/libsolution.so main

test: run
# https://github.com/mrtazz/checkmake # use nix
	checkmake Makefile
	checkmake lib/Makefile

.PHONY: all test clean
