all: fast slow


fast: fast.c
	gcc -O3 -g -o $@ $< -lpapi

slow: slow.c
	gcc -O3 -g -o $@ $< -lpapi -lm
