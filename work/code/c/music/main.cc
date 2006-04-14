#include <SDL.h>
#include <iostream>
#include <cstdlib>
#include <map>
#include <memory>
#include <unistd.h>

#include "Synth.h"
#include "NoteList.h"

using std::auto_ptr;

#define DIE { std::cerr << "Died.\n"; exit(1); }

NoteList NOTELIST;
float TIME0 = 0;
float BEAT = 0;
FluidSynth SYNTH("airfont.sf2");
FluidSynthTrack* TRACK;
FluidSynthTrack* DRUMS;
SDL_TimerID TIMER;

void init_sdl()
{
	std::cout << "Starting SDL video\n";
	SDL_Init(SDL_INIT_VIDEO | SDL_INIT_TIMER);
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

float time_now() {
	return SDL_GetTicks() / 1000.0;
}

float bpm2dt(float bpm) {
	return 60.0/bpm;
}

float find_beat() {
	float bestcor = HUGE_VAL, bestbeat = 0;
	for (float bpm = 60.0; bpm < 600.0; bpm += 1) {
		float dt = bpm2dt(bpm);
		float cor = NOTELIST.correlate(dt, TIME0);
		if (cor < bestcor) { bestcor = cor;  bestbeat = bpm; }
	}
	std::cout << "BPM: " << bestbeat << " (correlation = " << bestcor << ")\n";
	return bestbeat;
}

Uint32 callback(Uint32 interval, void* param) {
	std::cout << "Dng\n";
	DRUMS->note_off(60);
	DRUMS->note_on(60);
	return Uint32(1000*BEAT);
}

int main()
{
	TRACK = SYNTH.new_track();
	DRUMS = SYNTH.new_track();

	DRUMS->set_patch(115);
	
	init_keymap();
	init_sdl();

	SDL_Event e;
	while (SDL_WaitEvent(&e)) {
		if (e.type == SDL_KEYDOWN) {
			if (e.key.keysym.sym == SDLK_ESCAPE) quit();
			keymap_t::iterator i = KEYMAP.find(e.key.keysym.sym);
			if (i != KEYMAP.end()) {
				TRACK->note_on(i->second);
			}
			if (TIME0 == 0) TIME0 = time_now();
			NOTELIST.add_note(NoteOn(i->second, 100, time_now()));
			if (NOTELIST.size() == 16) {
				BEAT = bpm2dt(find_beat());
				float time = time_now();
				float nextbeat = TIME0;
				while (nextbeat < time) nextbeat += BEAT;
				SDL_RemoveTimer(TIMER);
				TIMER = SDL_AddTimer(Uint32(1000*(nextbeat - time)), &callback, NULL);
				NOTELIST.clear();
			}
		}
		if (e.type == SDL_KEYUP) {
			keymap_t::iterator i = KEYMAP.find(e.key.keysym.sym);
			if (i != KEYMAP.end()) {
				TRACK->note_off(i->second);
			}
		}
	}
}
