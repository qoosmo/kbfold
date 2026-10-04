all: sumfri.pdf

sumfri.pdf: main.tex refs.bib sections/*.tex
	latexmk -pdf -interaction=nonstopmode main.tex
	cp main.pdf sumfri.pdf

clean:
	latexmk -C

.PHONY: all clean
