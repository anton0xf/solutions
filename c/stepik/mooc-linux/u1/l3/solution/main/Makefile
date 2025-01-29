all: solution

solution: solution.c
	gcc solution.c -ldl -Wl,-rpath,. -fPIC -o solution

clean:
	-rm -fv solution

test:
# https://github.com/mrtazz/checkmake # use nix
	checkmake Makefile

.PHONY: all test clean
