#include <iostream>
#include <fstream>
#include <sstream>
#include <GL/glew.h>
#include <SDL.h>
#include <sys/mman.h>

void init() 
{
	SDL_Init(SDL_INIT_VIDEO);
	SDL_SetVideoMode(640, 480, 0, SDL_OPENGL);

	glMatrixMode(GL_PROJECTION);
	glLoadIdentity();
	gluOrtho2D(-4,4,-3,3);
	glMatrixMode(GL_MODELVIEW);
	glLoadIdentity();
}

void init_shaders()
{
	GLhandleARB frag = glCreateShaderObjectARB(GL_FRAGMENT_SHADER);
	
	std::ifstream fin("frag.glsl");
	std::stringbuf buf;
	fin.get(buf, '\0');
	fin.close();
	
	int len = buf.str().size();
	const char* str = buf.str().c_str();
	glShaderSourceARB(frag, 1, &str, &len);

	glCompileShaderARB(frag);

	int status;
	glGetObjectParameterivARB(frag, GL_OBJECT_COMPILE_STATUS_ARB, &status);
	if (!status) {
		std::cout << "Failed to compile:\n";
		char buf[1024];
		int len;
		glGetInfoLogARB(frag, 1023, &len, buf);
		buf[len] = 0;
		std::cout << buf;
	}

	//////
	
	GLhandleARB prog = glCreateProgramObjectARB();
	
	glAttachObjectARB(prog, frag);

	glLinkProgramARB(prog);

	glUseProgramObjectARB(prog);
	
	glGetObjectParameterivARB(prog, GL_OBJECT_LINK_STATUS_ARB, &status);
	if (!status) {
		std::cout << "Failed to link\n";
		char buf[1024];
		int len;
		glGetInfoLogARB(prog, 1023, &len, buf);
		buf[len] = 0;
		std::cout << buf;
	}
}

void draw()
{
	glBegin(GL_QUADS);
		glColor3f(1,1,1);
		glVertex2f(-1,-1);
		glColor3f(1,1,0);
		glVertex2f(-1,1);
		glColor3f(1,0,1);
		glVertex2f(1,1);
		glColor3f(1,0,0);
		glVertex2f(1,-1);
	glEnd();
}

void events()
{
	SDL_Event e;
	while (SDL_PollEvent(&e)) {
		if (e.type == SDL_QUIT ||
			e.type == SDL_KEYDOWN && e.key.keysym.sym == SDLK_ESCAPE) {
			SDL_Quit();
			exit(0);
		}
	}
}

int main(int argc, char** argv) {
	init();
	glewInit();

	if (GLEW_ARB_vertex_shader && GLEW_ARB_fragment_shader) {
		std::cout << "Loaded extensions ARB_vertex_shader and ARB_fragment_shader\n";
	}
	else {
		std::cout << "Couldn't load extensions\n";
		SDL_Quit();
		exit(1);
	}

	init_shaders();

	while (true) {
		events();
		glClear(GL_COLOR_BUFFER_BIT);
		draw();
		SDL_GL_SwapBuffers();
	}
}
