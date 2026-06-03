SOURCES = main.tex
PDF = main.pdf

top: main.pdf

%.pdf:  %.tex src/*.tex main.sty
	latexmk -bibtex -synctex=1 -interaction=nonstopmode  -pdf --shell-escape $<

cleanup:
	latexmk -C

clean: cleanup
	rm -f $(PDF)
