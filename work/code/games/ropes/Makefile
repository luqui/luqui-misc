ODEDIR = /home/luqui/devel/ode
CXXFLAGS = -g -Wall `sdl-config --cflags` -I$(ODEDIR)/include
LDLIBS = `sdl-config --libs` -L$(ODEDIR)/lib -lode -lGL -lGLU -lSDL_image -lSDL_mixer

CXXFILES = main.cc geometry.cc input.cc objects.cc drawing.cc level.cc
HFILES = common.h drawing.h geometry.h input.h objects.h physics.h player.h vec.h tweak.h level.h effects.h

all: ropes

ropes: $(HFILES) $(CXXFILES)
	g++ $(CXXFLAGS) $(CXXFILES) -o $@ $(LDLIBS)
