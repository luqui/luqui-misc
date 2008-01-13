all:

%: %.hs dummy
	ghc --make $@ Fregl/RTSHook.c -lSDL_image

dummy:


clean:
	rm -f Fregl/*.o Fregl/*.hi examples/*.o examples/*.hi

