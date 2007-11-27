all: test bounce

test: .dummy
	ghc --make -O2 test

bounce: .dummy
	ghc --make -O2 bounce

demo: .dummy
	ghc --make -O2 demo

clean: .dummy
	rm -f *.hi *.o Fregl/*.hi Fregl/*.o

.dummy:


