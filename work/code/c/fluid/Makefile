CXXFLAGS = -Wall -O2 `sdl-config --cflags`
LDLIBS = -lSDL -lGL -lGLU -lSDL_image

all: fluid

%.o: %.cc Texture.h config.h FluidGrid.h
	$(CXX) -c $(CXXFLAGS) $<

fluid: main.o Texture.o
	$(CXX) -o $@ $^ $(LDLIBS)
