%: %.hs
	ghc --make -O -o $@ $<
	rm -f $@.hi $@.o

tictactoe: tictactoe.hs
	ghc --make -O -o $@ $<
	rm -f $@.hi $@.o

clean:
	rm -f *.hi *.o

