view: lambda.dvi
	xdvi lambda.dvi

lambda.tex: lambda.ml
	ocamlweb --latex-option novisiblespaces --class-options 11pt --noindex -s lambda.ml -p "\newcommand{\bibfieldurl}[1]{~\url{#1}}" -o $@

lambda.dvi: lambda.tex
	latex lambda.tex