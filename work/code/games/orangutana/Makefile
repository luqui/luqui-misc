CCFLAGS = -g `sdl-config --cflags`
LDLIBS = -lode `sdl-config --libs`

all: orangutana

orangutana: main.cc
	gcc $(CCFLAGS) -o $@ $(LDLIBS) $^
