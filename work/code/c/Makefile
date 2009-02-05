CXXFLAGS = -O3

collide: collide.cc
	g++ -O2 -o collide collide.cc `sdl-config --libs --cflags` -lGL -lGLU -lode -g

hamiltonian: hamiltonian.cc
	g++ -o hamiltonian hamiltonian.cc `sdl-config --libs --cflags` -lGL -lGLU -g
