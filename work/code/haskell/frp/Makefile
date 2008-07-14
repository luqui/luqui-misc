all:

%: %.hs dummy
	ghc -O2 --make $@ Fregl/RTSHook.c -lSDL_image -lSDL_ttf

dummy:


clean:
	rm -f Fregl/*.o Fregl/*.hi examples/*.o examples/*.hi *.o *.hi

