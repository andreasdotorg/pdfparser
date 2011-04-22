%.vo: %.v
	coqc $<

all: main

parser.vo: SfLib.vo sublist.vo
pdftype.vo: SfLib.vo
sublist.vo: SfLib.vo
pdfparser.vo: SfLib.vo parser.vo pdftype.vo
parser.ml: pdfparser.vo
parser.mli: pdfparser.vo
allparser.ml: parser.ml preamble.ml pdfparser.vo
	cat preamble.ml parser.ml > allparser.ml
allparser.mli: parser.mli ipreamble.ml pdfparser.vo
	cat ipreamble.ml parser.mli > allparser.mli
allparser.cmi: allparser.mli
	ocamlfind ocamlc -package batteries -package batteries.syntax -syntax camlp4o -c allparser.mli
allparser.cmo: allparser.ml
	ocamlfind ocamlc -package batteries -package batteries.syntax -syntax camlp4o -c allparser.ml
main: allparser.cmo main.ml
	ocamlfind ocamlc -package batteries -package batteries.syntax -syntax camlp4o -linkpkg allparser.cmo main.ml -o main


t: t.ml
	ocamlfind ocamlc -package batteries -package batteries.syntax -syntax camlp4o -linkpkg t.ml -o t
clean:
	-rm *.vo *.glob *~ *.cmi *.cmo allparser.ml allparser.mli t main