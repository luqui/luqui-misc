CXXFLAGS = -Wall -O2 -g `sdl-config --cflags`
LDLIBS = `sdl-config --libs` -lGL -lGLU -lode

all: ballo

ballo: main.o physics.o
	$(CXX) -o $@ $^ $(LDLIBS)
