LATEXMK ?= latexmk

.PHONY: all
all	: formalism.pdf

%.pdf : %.tex
	$(LATEXMK) $*.tex
	mv target/$*.pdf $*.pdf

.PHONY : clean
clean :
	rm -rf target
	rm -f *.pdf
