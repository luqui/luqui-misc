CXXFLAGS = -Wall -O2 `sdl-config --cflags`
LDLIBS = -lSDL -lGL -lGLU

all: main

main: main.cc FluidGrid.h config.h
	g++ $(CXXFLAGS) $< -o main $(LDLIBS)
