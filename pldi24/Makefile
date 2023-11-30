all: paper.pdf resources.pdf 

paper.pdf: paper.tex references.bib acmart.cls 
	latexmk -pdf paper.tex

resources.pdf: resources.tex acmart.cls references.bib 
	latexmk -pdf resources.tex

clean: 
	rm -f *.aux *.dtx *.bbx *.dbx *.bbl *.fdb_latexmk *.fls *.log *.out *~

realclean: 
	rm -f paper.pdf *.aux *.dtx *.bbx *.dbx *.bbl *.fdb_latexmk *.fls *.log *.out *~
