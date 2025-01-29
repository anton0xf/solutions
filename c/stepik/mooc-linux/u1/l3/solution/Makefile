all: run

run: libShared.so main/solution
	./main/solution libShared.so square 4

libShared.so:
	gcc shared.c --shared -fPIC -o libShared.so

main/solution: main/solution.c
	gcc main/solution.c -ldl -Wl,-rpath,. -fPIC -o main/solution

clean:
	-rm -fv libShared.so main/solution

test:
# https://github.com/mrtazz/checkmake # use nix
	checkmake Makefile
	checkmake main/Makefile

.PHONY: all test clean
