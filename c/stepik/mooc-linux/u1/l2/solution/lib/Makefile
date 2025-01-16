all: libsolution.so

libsolution.so:
	gcc -o libsolution.so --shared -fPIC solution.c

clean:
	-rm -fv libsolution.so

test: run
	checkmake Makefile

.PHONY: all test clean
