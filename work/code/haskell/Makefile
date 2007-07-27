%: %.hs
	ghc --make -O -o $@ $<
	rm -f $@.hi $@.o

%.pp.hs: %.hs
	cpp $< > $@

clean:
	rm -f *.hi *.o

