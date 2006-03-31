#include <SDL.h>
#include <iostream>
#include <cstdlib>
#include <map>
#include <memory>
#include <unistd.h>

#include "Synth.h"

using std::auto_ptr;

#define DIE { std::cerr << "Died.\n"; exit(1); }

void init_sdl()
{
	std::cout << "Starting SDL video\n";
	SDL_Init(SDL_INIT_VIDEO);
	SDL_SetVideoMode(640, 480, 0, 0);
}

typedef std::map<SDLKey, int> keymap_t;
keymap_t KEYMAP;

void init_keymap()
{
	std::cout << "Creating keymap\n";
	KEYMAP[SDLK_a] = 53;
	KEYMAP[SDLK_w] = 54;
	KEYMAP[SDLK_s] = 55;
	KEYMAP[SDLK_e] = 56;
	KEYMAP[SDLK_d] = 57;
	KEYMAP[SDLK_r] = 58;
	KEYMAP[SDLK_f] = 59;
	KEYMAP[SDLK_g] = 60;
	KEYMAP[SDLK_y] = 61;
	KEYMAP[SDLK_h] = 62;
	KEYMAP[SDLK_u] = 63;
	KEYMAP[SDLK_j] = 64;
	KEYMAP[SDLK_k] = 65;
	KEYMAP[SDLK_o] = 66;
	KEYMAP[SDLK_l] = 67;
}

void quit()
{
	SDL_Quit();
}

int main()
{
	auto_ptr<Synth> synth(new FluidSynth("airfont.sf2"));
	auto_ptr<SynthTrack> track(synth->new_track());

	init_keymap();
	init_sdl();

	SDL_Event e;
	while (SDL_WaitEvent(&e)) {
		if (e.type == SDL_KEYDOWN) {
			if (e.key.keysym.sym == SDLK_ESCAPE) quit();
			keymap_t::iterator i = KEYMAP.find(e.key.keysym.sym);
			if (i != KEYMAP.end()) {
				track->note_on(i->second);
			}
		}
		if (e.type == SDL_KEYUP) {
			keymap_t::iterator i = KEYMAP.find(e.key.keysym.sym);
			if (i != KEYMAP.end()) {
				track->note_off(i->second);
			}
		}
	}
}
