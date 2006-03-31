CXXFLAGS = -g `sdl-config --cflags`
LDLIBS = -lfluidsynth `sdl-config --libs`

all: music

music: main.o Synth.o
	$(CXX) $(CXXFLAGS) -o $@ $^ $(LDLIBS)
