#include <SDL.h>
#include <GL/gl.h>
#include <GL/glu.h>
#include <SDL_mixer.h>
#include <fftw3.h>
#include <stdlib.h>
#include <map>
#include <cstdlib>
#include <cmath>
#include <iostream>
#include <soy/Timer.h>

const int NBUFS = 32;
const int SAMPLES = 65536;

Mix_Chunk* CHANS[NBUFS];
Sint16* BUFS[NBUFS];

SDL_AudioSpec AUDIO;
fftw_complex* fourier;
fftw_complex* tmpfourier;
fftw_complex* tmpaudio;
double* audio;
fftw_plan PLAN;

int CURBUF = 0;

void channel_finished(int channel) {
	Mix_FreeChunk(CHANS[channel]);
	fftw_free(BUFS[channel]);
}

void gensound() {
	fftw_execute(PLAN);

	for (int i = 0; i < SAMPLES; i++) {
		audio[i] = tmpaudio[i][0];
	}

	double max = 0;
	for (int i = 0; i < SAMPLES; i++) {
		double samp = audio[i];
		if (fabs(samp) > max) max = fabs(samp);
	}

	Sint16* stream = (Sint16*)fftw_malloc(sizeof(Sint16) * SAMPLES);
	double scale = max > 0.9/NBUFS ? (0.9 / NBUFS) / max : 1;
	for (int i = 0; i < SAMPLES; i++) {
		double samp = audio[i];
		double fadein = i < 300 ? i/300.0 : 1;
		double fadeout = i > SAMPLES/2 ? double(SAMPLES-i)/(SAMPLES/2) : 1;
		stream[i] = Sint16(((1<<15)-1)*scale*fadein*fadeout*samp);
	}

	Mix_Chunk* chunk = Mix_QuickLoad_RAW((Uint8*)stream, sizeof(Sint16)*SAMPLES);
	int chan = Mix_PlayChannel(-1, chunk, 0);
	if (chan >= 0) {
		CHANS[chan] = chunk;
		BUFS[chan] = stream;
	}
	else {
		fftw_free(stream);
	}
}

void init_sdl()
{
	SDL_Init(SDL_INIT_VIDEO | SDL_INIT_AUDIO);
	SDL_SetVideoMode(1024,768,0,SDL_OPENGL | SDL_FULLSCREEN);
	SDL_ShowCursor(0);
	glMatrixMode(GL_PROJECTION);
	glLoadIdentity();
	gluOrtho2D(-2,2,-1.5,1.5);
	glMatrixMode(GL_MODELVIEW);
	glLoadIdentity();
	glEnable(GL_BLEND);
	glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
	
	int retval = Mix_OpenAudio(44100, AUDIO_S16SYS, 1, SAMPLES/NBUFS);
	if (retval < 0) {
		std::cerr << "Couldn't open audio driver: " << SDL_GetError() << "\n";
		SDL_Quit();
		exit(1);
	}

	Mix_AllocateChannels(NBUFS);
	Mix_ChannelFinished(&channel_finished);

	fourier    = (fftw_complex*)fftw_malloc(sizeof(fftw_complex) * SAMPLES);
	tmpfourier = (fftw_complex*)fftw_malloc(sizeof(fftw_complex) * SAMPLES);
	tmpaudio   = (fftw_complex*)fftw_malloc(sizeof(fftw_complex) * SAMPLES);
	audio      = (double*)fftw_malloc(sizeof(double) * SAMPLES);

	PLAN = fftw_plan_dft_1d(SAMPLES, fourier, tmpaudio, FFTW_BACKWARD, FFTW_ESTIMATE);
}

float P[10];
const float PM[10] = { 0, 1.5, 0, .5, 1.5,
					   0, 1.5, 0, .5, 1.5 };
const float PA[10] = { 2.0, 3.5, 3.5, 2.5, 4.7,
					   1.5, 3.5, 3.6, 2.5, 4.7 };
int iters = 10000;
float offset = 0;
typedef std::map<SDLKey, int> paramcoord_t;
paramcoord_t PARAMX;
paramcoord_t PARAMY;

void reset() {
	for (int i = 0; i < 10; i++) {
		P[i] = PM[i];
	}
}

bool PLAY = false;
bool WILLPLAY = false;
bool SUSTAIN = false;

void events()
{
	SDL_Event e;
	SDLMod mods = SDL_GetModState();
	while (SDL_PollEvent(&e)) {
		if (e.type == SDL_MOUSEMOTION) {
			Uint8* keys = SDL_GetKeyState(NULL);
			float dxf = float(e.motion.xrel)/640;
			float dyf = -float(e.motion.yrel)/512;

			if (mods & KMOD_SHIFT) {
				dxf /= 10;
				dyf /= 10;
			}
			if (mods & KMOD_CTRL) {
				dxf /= 100;
				dyf /= 100;
			}

			for (paramcoord_t::iterator i = PARAMX.begin(); i != PARAMX.end(); ++i) {
				if (keys[i->first]) {
					P[i->second] += PA[i->second]*dxf;
				}
			}
			for (paramcoord_t::iterator i = PARAMY.begin(); i != PARAMY.end(); ++i) {
				if (keys[i->first]) {
					P[i->second] += PA[i->second]*dyf;
				}
			}
		}
		if (e.type == SDL_KEYDOWN) {
			if (e.key.keysym.sym == SDLK_ESCAPE) {
				SDL_Quit();
				exit(0);
			}
			if (e.key.keysym.sym == SDLK_r) {
				reset();
			}
			if (e.key.keysym.sym == SDLK_MINUS) {
				iters /= 2;
			}
			if (e.key.keysym.sym == SDLK_EQUALS) {
				iters *= 2;
			}
		}
		if (e.type == SDL_MOUSEBUTTONDOWN) {
			if (e.button.button == SDL_BUTTON_LEFT) {
				WILLPLAY = true;
			}
		}
	}

	int buts = SDL_GetMouseState(0, 0);
	if (buts & SDL_BUTTON(1)) {
		PLAY = true;
	}
	else {
		PLAY = false;
	}

	Uint8* keys = SDL_GetKeyState(NULL);
	SUSTAIN = keys[SDLK_SPACE];
}

float randrange(float a, float b)
{
	float r = float(rand()) / RAND_MAX;
	return a + (b - a) * r;
}

void drift(float amt)
{
	for (int i = 0; i < 10; i++) {
		P[i] += randrange(-amt, amt) * PA[i];
	}
}

void set_palette(float phase)
{
	phase += offset;
	glColor4f(
			0.5*sin(2*M_PI*phase)+0.5,
			0.5*cos(5*M_PI*phase)+0.5,
			0.5*sin(11*M_PI*phase)+0.5,
			0.4);
}

void draw_attractor(float x, float y)
{
	for (int i = 0; i < SAMPLES; i++) {
		tmpfourier[i][0] = tmpfourier[i][1] = 0;
	}
	
	glPointSize(2.0);
	glBegin(GL_POINTS);
	glColor4f(1,0,0,0.6);
	glVertex2f(0,0);
	for (int i = 0; i < iters; i++) {
		float nx = P[0] - y*(P[1] * x*x + P[2] * x*y + P[3] * y*y + P[4] * x*x*y);
		float ny = P[5] + x*(P[6] * x*x + P[7] * x*y + P[8] * y*y + P[9] * y*y*x);
		x = nx;
		y = ny;
		do {
			float fx = x/4, fy = y/3;
			float r = log(sqrt(fx*fx + fy*fy)+1);
			if (r >= 1 || !std::isfinite(r)) break;
			float mag = r > 0.2 ? 0.2/r : 1;
			tmpfourier[int(r*SAMPLES)/10][0] += 0.01*mag*cos(2*M_PI*i/iters);
			tmpfourier[int(r*SAMPLES)/10][1] += 0.01*mag*sin(2*M_PI*i/iters);
		} while (false);

		set_palette(float(i)/iters);
		float rad = sqrt(x*x+y*y);
		float newrad = log(rad+1);
		glVertex2f(newrad * x/rad, newrad * y/rad);
	}
	glEnd();
	
	for (int i = 0; i < SAMPLES; i++) {
		float mag = sqrt(tmpfourier[i][0]*tmpfourier[i][0] + tmpfourier[i][1]*tmpfourier[i][1]);
		float newmag = log(mag+1);
		float scale = mag > 0 ? newmag/mag : 0;
		if (SUSTAIN) {
			fourier[i][0] *= 0.99;
			fourier[i][1] *= 0.99;
		}
		else {
			fourier[i][0] *= 0;
			fourier[i][1] *= 0;
		}
		if (PLAY || WILLPLAY) {
			WILLPLAY = false;
			fourier[i][0] += tmpfourier[i][0]*scale;
			fourier[i][1] += tmpfourier[i][1]*scale;
		}
	}
}

void draw()
{
	draw_attractor(0,0);
	/*
	glPointSize(4.0);
	glColor3f(1,1,1);
	glBegin(GL_POINTS);
	for (int i = 0; i < 5; i++) {
		glVertex2f((P[i]-PM[i])/PA[i], (P[i+5]-PM[i+5])/PA[i+5]);
	}
	glEnd();
	*/
}

int main()
{
	Timer timer;
	std::cout << "Initing\n";
	init_sdl();
	std::cout << "Inited\n";
	PARAMX[SDLK_a] = 0;
	PARAMY[SDLK_a] = 5;
	PARAMX[SDLK_s] = 1;
	PARAMY[SDLK_s] = 6;
	PARAMX[SDLK_d] = 2;
	PARAMY[SDLK_d] = 7;
	PARAMX[SDLK_f] = 3;
	PARAMY[SDLK_f] = 8;
	PARAMX[SDLK_g] = 4;
	PARAMY[SDLK_g] = 9;
	reset();
	SDL_PauseAudio(0);

	float time = 0.05;
	timer.init();
	while(true) {
		events();
		offset += 0.00002;
		glClear(GL_COLOR_BUFFER_BIT);
		draw();
		SDL_GL_SwapBuffers();
		
		time -= timer.get_time_diff();
		if (time < 0) {
			gensound();
			time = 0.05;
		}
	}
	SDL_Quit();
}
