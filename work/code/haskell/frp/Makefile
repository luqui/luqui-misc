all:

%: %.hs dummy
	ghc --make $@ Fregl/RTSHook.c -lSDL_image -lSDL_ttf

dummy:


clean:
	rm -f Fregl/*.o Fregl/*.hi examples/*.o examples/*.hi Malbono/*.o Malbono/*.hi *.o *.hi

