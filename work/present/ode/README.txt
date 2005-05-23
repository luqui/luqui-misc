To compile these examples on linux, just use the Makefile:

    % cd examples
    % make collide  # or force, or torque, or falling_ball

To compile on windows, go to libsdl.org and download the SDL 1.2 Win32 
development library: SDL-devel-1.2.8-VC6.zip and unpack it somewhere.

Start a new "Win32 application" project in VC++. Set the runtime to
"Multi-Threaded DLL" in Project Settings|C/C++|Code Generation

Add the SDL include directory (where you extracted the zip\include) to
Project Settings|Preprocessor|Additional include directories.

Add the SDL library directory (where you extracted the zip\lib) to
Project Settings|Linker|Additional library directories.

Add the following libraries to Project Settings|Linker|Additional library
dependencies:

    SDL.lib SDLmain.lib OpenGL32.lib GLU32.lib GLX.lib

Copy SDL.dll into the project directory.

Add main.h and the source file you want to compile to the project, compile,
and run.
