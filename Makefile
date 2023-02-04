LATEXMK ?= latexmk
AGDA    ?= agda

.PHONY: all
all : formalism.pdf all.agdai

%.pdf : %.tex
	$(LATEXMK) $*.tex
	mv build/$*.pdf $*.pdf

%.agdai : %.agda
	$(AGDA) $*.agda

.PHONY : clean
clean :
	rm -rf build
	rm -f *.pdf
	rm -f *.agdai
