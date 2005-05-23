CXX = g++
CXXFLAGS = -I/home/fibonaci/devel/ode/include `sdl-config --cflags`
LDLIBS = -L/home/fibonaci/devel/ode/lib `sdl-config --libs` -lGL -lGLU -lode

%: %.cpp setup.h
	$(CXX) $(CXXFLAGS) $< $(LDLIBS) -o $@
