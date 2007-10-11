%: %.hs
	ghc --make -O2 -o $@ $<
	rm -f $@.hi $@.o

%.pp.hs: %.hs
	cpp $< > $@

clean:
	rm -f *.hi *.o

