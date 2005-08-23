all: closure

closure: closure.hs
	ghc -fglasgow-exts -package mtl -o $@ $<

clean:
	rm -f closure.hi closure.o
