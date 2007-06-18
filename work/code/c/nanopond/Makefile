all: nanopond

nanopond: nanopond-1.9.c
	gcc $^ -O3 `sdl-config --cflags` -o $@ `sdl-config --libs`
