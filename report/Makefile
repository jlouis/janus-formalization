all:
	cd .. && $(MAKE) doc
	pdflatex master.tex
	bibtex master
	pdflatex master.tex
	pdflatex master.tex
