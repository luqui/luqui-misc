CXXFLAGS = -Wall -O2 `sdl-config --cflags`
LDLIBS = -lSDL -lGL -lGLU -lSDL_image

all: fluid

fluid: main.o Texture.o
	$(CXX) -o $@ $^ $(LDLIBS)
