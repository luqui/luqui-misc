LDLIBS = `sdl-config --libs` -lGL -lGLU
CXXFLAGS = `sdl-config --cflags`

all: recursiverse

clean:
	rm -f *.o

recursiverse: Window.o main.o
	g++ $(CXXFLAGS) $(LDLIBS) -o $@ $^
