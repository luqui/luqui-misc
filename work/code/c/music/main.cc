#include <fluidsynth.h>
#include <SDL.h>
#include <iostream>
#include <cstdlib>
#include <map>
#include <unistd.h>

#define DIE { std::cerr << "Died.\n"; exit(1); }

fluid_settings_t* SETTINGS;
fluid_synth_t* SYNTH;

void init_fluid()
{
	std::cout << "Creating settings\n";
	SETTINGS = new_fluid_settings();
	if (!SETTINGS) DIE;
	fluid_settings_setstr(SETTINGS, "audio.driver", "oss");
	fluid_settings_setint(SETTINGS, "audio.periods", 16);
	fluid_settings_setint(SETTINGS, "audio.period-size", 64);

	std::cout << "Creating fluidsynth\n";
	SYNTH = new_fluid_synth(SETTINGS);
	if (!SYNTH) DIE;
	
	std::cout << "Loading samples\n";
	int sfid = fluid_synth_sfload(SYNTH, "airfont.sf2", 1);
	if (sfid == -1) DIE;
	
	std::cout << "Starting audio driver\n";
	fluid_audio_driver_t* driver = new_fluid_audio_driver(SETTINGS, SYNTH);
	if (!driver) DIE;
}

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
	delete_fluid_synth(SYNTH);
	delete_fluid_settings(SETTINGS);
}

int main()
{
	init_fluid();
	init_keymap();
	init_sdl();

	SDL_Event e;
	while (SDL_WaitEvent(&e)) {
		if (e.type == SDL_KEYDOWN) {
			if (e.key.keysym.sym == SDLK_ESCAPE) quit();
			keymap_t::iterator i = KEYMAP.find(e.key.keysym.sym);
			if (i != KEYMAP.end()) {
				fluid_synth_noteon(SYNTH, 0, i->second, 100);
			}
		}
		if (e.type == SDL_KEYUP) {
			keymap_t::iterator i = KEYMAP.find(e.key.keysym.sym);
			if (i != KEYMAP.end()) {
				fluid_synth_noteoff(SYNTH, 0, i->second);
			}
		}
	}
}
