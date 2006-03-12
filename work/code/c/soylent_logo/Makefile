all: logo

logo: logo.cc
	g++ -O -g `sdl-config --cflags` -o $@ $^ `sdl-config --libs` -lGL -lGLU
