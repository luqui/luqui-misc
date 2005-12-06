all: doc.dvi

doc.dvi: doc.tex dog-cat-tree.eps base-tree-example.eps adjoining-substitution.eps \
	 tense-features.eps conjunction.eps
	latex doc.tex
	latex doc.tex

doc.pdf: doc.dvi
	dvipdf doc.dvi

%.eps: %.dia
	dia -e $@ $<

clean:
	rm -f doc.log doc.aux *.eps
