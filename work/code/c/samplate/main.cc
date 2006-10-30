#include <fftw3.h>
#include <SDL.h>
#include <GL/gl.h>
#include <GL/glu.h>
#include <cstdlib>
#include <cassert>
#include <iostream>
#include <string>
#include <stdlib.h>

SDL_AudioSpec AUDIO;
int POS = 0;
double R = 2.9;

double clamp(double val, double min, double max) {
	if (val < min) val = min;
	if (val > max) val = max;
	return val;
}

fftw_complex* load_wav(std::string wav, int* size) {
	SDL_AudioSpec spec;
	Uint32 length;
	Uint8* buffer;

	if (!SDL_LoadWAV(wav.c_str(), &spec, &buffer, &length)) {
		std::cerr << "Couldn't open " << wav << ": " << SDL_GetError() << "\n";
		return 0;
	}

	std::cout << "Specs for " << wav << ":\n";
	std::cout << "  Frequency: " << spec.freq << " Hz\n";
	std::cout << "  Format:    ";
	switch (spec.format) {
		case AUDIO_U8:     std::cout << "U8"; break;
		case AUDIO_S8:     std::cout << "S8"; break;
		case AUDIO_U16LSB: std::cout << "U16LSB"; break;
		case AUDIO_S16LSB: std::cout << "S16LSB"; break;
		case AUDIO_U16MSB: std::cout << "U16MSB"; break;
		case AUDIO_S16MSB: std::cout << "S16MSB"; break;
		default:           std::cout << "Unknown (that's bad)";  break;
	}
	std::cout << "\n";
	std::cout << "    (System is " << (AUDIO_U16SYS == AUDIO_U16MSB ? "MSB" : "LSB") << ")\n";
	std::cout << "  Channels:  " << (int)spec.channels << "\n";

	if (spec.format == AUDIO_S16LSB) {
		int samples = length / 2;
		Sint16* sbuffer = (Sint16*)buffer;
		fftw_complex* ret = (fftw_complex*)fftw_malloc(sizeof(fftw_complex) * samples);

		for (int i = 0; i < samples; i++) {
			ret[i][0] = sbuffer[i] / 32767.0;
			ret[i][1] = 0;
		}
		SDL_FreeWAV(buffer);
		
		*size = samples;
		return ret;
	}
	else {
		std::cerr << "I don't grok that format\n";
		SDL_FreeWAV(buffer);
		return 0;
	}
}


Sint16* BUFSTART = 0;
Sint16* BUFFER = 0;
int BUFFER_LENGTH = 0;
void gensound(void* data, Uint8* instream, int len) 
{
	Sint16* stream = (Sint16*)instream;
	len /= 2;

	while (len > 0 && BUFFER_LENGTH > 0) {
		*stream++ = *BUFFER++;
		len--;
		BUFFER_LENGTH--;
	}
	
	if (BUFSTART && BUFFER_LENGTH == 0) {
		fftw_free(BUFSTART);
		BUFSTART = BUFFER = 0;
	}

	while (len > 0) {
		*stream++ = 0;
		len--;
	}
}

// Ugh, threading nightmares
void play_buffer(Sint16* buf, int length) {
	BUFSTART = BUFFER = buf;
	BUFFER_LENGTH = length;

	// Block until we're done playing
	while (BUFSTART) {
		SDL_Delay(100);
	}
}

void play_wave(fftw_complex* wave, int length) {
	double magnitude = 0;
	for (int i = 0; i < length; i++) {
		if (fabs(wave[i][0]) > magnitude) {
			magnitude = fabs(wave[i][0]);
		}
	}
	
	Sint16* buf = (Sint16*)fftw_malloc(sizeof(Sint16) * length);
	for (int i = 0; i < length; i++) {
		buf[i] = Sint16(32767 * (wave[i][0] / magnitude));
	}

	play_buffer(buf, length);
}

void init()
{
	SDL_Init(SDL_INIT_VIDEO | SDL_INIT_AUDIO);
	SDL_SetVideoMode(800, 600, 0, SDL_OPENGL);

	glMatrixMode(GL_PROJECTION);
	glLoadIdentity();
	gluOrtho2D(-1, 1, -1, 1);
	glMatrixMode(GL_MODELVIEW);
	glLoadIdentity();

	glClear(GL_COLOR_BUFFER_BIT);

	SDL_AudioSpec desired;
		desired.freq = 44100;
		desired.format = AUDIO_S16SYS;
		desired.channels = 1;
		desired.samples = 8192;
		desired.callback = &gensound;
		desired.userdata = 0;
	
	int retval = SDL_OpenAudio(&desired, &AUDIO);
	if (retval < 0) {
		std::cerr << "Couldn't open audio driver: " << SDL_GetError() << "\n";
		SDL_Quit();
		exit(1);
	}
}

void events()
{
	SDL_Event e;
	while (SDL_PollEvent(&e)) {
		if (e.type == SDL_KEYDOWN && e.key.keysym.sym == SDLK_ESCAPE) {
			SDL_Quit();
			exit(0);
		}
	}
}

fftw_complex* forward_fourier(fftw_complex* in, int length) {
	fftw_complex* out = (fftw_complex*)fftw_malloc(sizeof(fftw_complex) * length);
	fftw_plan plan = fftw_plan_dft_1d(length, in, out, FFTW_FORWARD, FFTW_ESTIMATE);
	fftw_execute(plan);
	return out;
}

fftw_complex* backward_fourier(fftw_complex* in, int length) {
	fftw_complex* out = (fftw_complex*)fftw_malloc(sizeof(fftw_complex) * length);
	fftw_plan plan = fftw_plan_dft_1d(length, in, out, FFTW_BACKWARD, FFTW_ESTIMATE);
	fftw_execute(plan);
	return out;
}

void normalize(fftw_complex* in, int length) {
	double maxmag = 0;
	for (int i = 0; i < length; i++) {
		double mag = in[i][0]*in[i][0] + in[i][1]*in[i][1];
		if (mag > maxmag) maxmag = mag;
	}
	
	for (int i = 0; i < length; i++) {
		in[i][0] /= maxmag;
		in[i][1] /= maxmag;
	}
}

fftw_complex* interpolate(fftw_complex* f, fftw_complex* g, int length, double alpha) {
	fftw_complex* ret = (fftw_complex*)fftw_malloc(sizeof(fftw_complex) * length);
	for (int i = 0; i < length; i++) {
		ret[i][0] = ret[i][1] = 0;
	}

	std::cout << "Smoothly interpolating " << length << " samples (this might take a little while)\n";

	double alpha1 = 1 / alpha;
	int lp = (length-1)/2;

	glColor3f(1,0.3,0);
	glBegin(GL_POINTS);
	for (int x = -lp; x <= lp; x++) {
		if (abs(x) % 500 == 0) {
			SDL_GL_SwapBuffers();
		}

		double real = 0;
		double imag = 0;
		
		double dminIf = clamp((-alpha * lp - x)/(alpha - 1), -lp, lp);
		double dmaxIf = clamp(( alpha * lp - x)/(alpha - 1), -lp, lp);
		if (dminIf > dmaxIf) { std::swap(dminIf, dmaxIf); }

		int minIf = int(std::ceil(dminIf));
		int maxIf = int(std::floor(dmaxIf));

		for (int If = minIf; If <= maxIf; If++) {
			int Ig = If + int((x - If) * alpha1);
			int Pf = If < 0 ? length + If : If;
			int Pg = Ig < 0 ? length + Ig : Ig;
			real += f[Pf][0] * g[Pg][0] - f[Pf][1] * g[Pg][1];
			imag += f[Pf][0] * g[Pg][1] + f[Pf][1] * g[Pg][0];
		}
		
		int Px = x < 0 ? length - x : x;
		ret[Px][0] = real;
		ret[Px][1] = imag;
		
		glVertex2f(double(x)/lp, 1e9*real);
	}
	glEnd();

	std::cout << "\nDone.\n";
	

	return ret;
}

void write_wave(std::string file, fftw_complex* wave, int length) {
	std::cout << "Writing wave data to " << file << "\n";
	SDL_RWops* fh = SDL_RWFromFile(file.c_str(), "w");
	if (!fh) {
		std::cerr << "Couldn't open " << file << ": " << SDL_GetError() << "\n";
		return;
	}
	SDL_RWwrite(fh, &length, sizeof(int), 1);
	SDL_RWwrite(fh, wave, sizeof(fftw_complex), length);
	SDL_RWclose(fh);
}

fftw_complex* read_wave(std::string file, int* length) {
	std::cout << "Reading wave data from " << file << "\n";
	SDL_RWops* fh = SDL_RWFromFile(file.c_str(), "r");
	if (!fh) {
		std::cerr << "Couldn't open " << file << ": " << SDL_GetError() << "\n";
		return 0;
	}
	SDL_RWread(fh, length, sizeof(int), 1);
	fftw_complex* ret = (fftw_complex*)fftw_malloc(sizeof(fftw_complex) * *length);
	SDL_RWread(fh, ret, sizeof(fftw_complex), *length);
	SDL_RWclose(fh);
	return ret;
}

void interpolate(std::string a, std::string b, bool quiet) {
	int lowlen;
	fftw_complex* lowc = load_wav(a, &lowlen);
	
	int hilen;
	fftw_complex* hic  = load_wav(b, &hilen);
	
	int midlen = std::min(lowlen, hilen);
	
	fftw_complex* lowcf = forward_fourier(lowc, midlen);
	normalize(lowcf, midlen);
	fftw_complex* hicf  = forward_fourier(hic, midlen);
	normalize(hicf, midlen);
	
	fftw_complex* midcf = interpolate(lowcf, hicf, midlen, 0.5);
	fftw_complex* midc  = backward_fourier(midcf, midlen);

	write_wave("interpolated.fcad", midc, midlen);

	fftw_free(lowcf);
	fftw_free(hicf);
	fftw_free(midcf);

	if (!quiet) {
		SDL_PauseAudio(0);
		play_wave(lowc, lowlen);
		play_wave(hic, hilen);
		play_wave(midc, midlen);
	}

	fftw_free(lowc);
	fftw_free(hic);
	fftw_free(midc);
}

void play_fcad(std::string file) {
	int length;
	fftw_complex* wave = read_wave(file, &length);
	SDL_PauseAudio(0);
	play_wave(wave, length);
	fftw_free(wave);
}

int main(int argc, char** argv)
{
	init();

	if (argc == 3) {
		interpolate(argv[1], argv[2], false);
	}
	else if (argc == 4 && std::string(argv[1]) == "-q") {
		interpolate(argv[2], argv[3], true);
	}
	else if (argc == 2) {
		play_fcad(argv[1]);
	}
	else {
		std::cerr << "Huh?\n";
	}
}
