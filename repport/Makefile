TEX = latexmk -pdf

all: repport.pdf

repport.pdf: repport.tex  title.tex
	$(TEX) repport.tex

.PHONY: clean

clean:
	rm -f *.aux *.log *.toc *.pdf *.bbl *.blg *.out *~  *.pdf *.f* *.gz