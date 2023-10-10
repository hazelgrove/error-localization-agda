LATEXMK ?= latexmk
AGDA    ?= agda

.PHONY: all
all : formalism.pdf all.agdai

%.pdf : formalism/%.tex
	cd formalism && $(LATEXMK) $*.tex
	mv formalism/build/$*.pdf $*.pdf

%.agdai : %.agda
	$(AGDA) $*.agda

.PHONY : clean
clean :
	rm -rf formalism/build
	rm -f *.pdf
	rm -f *.agdai
