all: test bounce

test: .dummy
	ghc --make -O2 test

bounce: .dummy
	ghc --make -O2 bounce

clean: .dummy
	rm -f *.hi *.o Fregl/*.hi Fregl/*.o

.dummy:


