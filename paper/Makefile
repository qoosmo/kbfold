all: kbfold.pdf

kbfold.pdf: main.tex refs.bib sections/*.tex
	latexmk -pdf -interaction=nonstopmode main.tex
	cp main.pdf kbfold.pdf

clean:
	latexmk -C

.PHONY: all clean
