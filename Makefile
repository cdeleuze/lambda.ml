clean:
	rm -f *.tex *.log *.aux *.cmi *.cmo

view: lambda.dvi
	xdvi lambda.dvi

pdf: lambda.pdf
	mupdf lambda.pdf

lambda.tex: lambda.ml
	ocamlweb --encoding latin1 --latex-option novisiblespaces --class-options 11pt --noindex -s lambda.ml -p "\newcommand{\bibfieldurl}[1]{~\url{#1}}" -o $@

# so that \citation's are ready for next latex run
lambda.aux: lambda.tex
	latex lambda.tex

lambda.dvi: lambda.tex lambda.aux
	latex lambda.tex

lambda.pdf: lambda.tex lambda.aux
	pdflatex lambda.tex

lambda: lambda.ml
	ocamlc -pp camlp4o -o $@ $<
