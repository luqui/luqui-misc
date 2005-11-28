all: doc.dvi

doc.dvi: doc.tex dog-cat-tree.eps
	latex doc.tex
	latex doc.tex

%.eps: %.dia
	dia -e $@ $<

clean:
	rm -f doc.log doc.aux *.eps
