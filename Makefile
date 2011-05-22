.PHONY: all clean allcoq

Vm := parser pdfparser pdftype SfLib sublist
Vs := $(Vm:%=%.v)

all: allcoq main

allcoq: Makefile.coq $(Vs)
	make -f Makefile.coq all

Makefile.coq: Makefile $(Vs)
	coq_makefile $(Vs) -o Makefile.coq

clean:
	make -f Makefile.coq clean
	rm Makefile.coq
	echo "remaining: " *~ *.cmi *.cmo allparser.m* ? mai*
	-rm *~ *.cmi *.cmo allparser.ml allparser.mli t main

# dep rule: extraction depends on pdfparser.vo, which should depend on most coq files
pdfparser.vo: allcoq

parser.ml: pdfparser.vo
parser.mli: pdfparser.vo
allparser.ml: parser.ml preamble.ml pdfparser.vo
	cat preamble.ml parser.ml > allparser.ml
allparser.mli: parser.mli ipreamble.ml pdfparser.vo
	cat ipreamble.ml parser.mli > allparser.mli
allparser.cmi: allparser.mli
	ocamlfind opt -package batteries -package batteries.syntax -syntax camlp4o -c allparser.mli
allparser.cmx: allparser.ml
	ocamlfind opt -package batteries -package batteries.syntax -syntax camlp4o -c allparser.ml
main: allparser.cmx main.ml
	ocamlfind opt -package batteries -package batteries.syntax -syntax camlp4o -linkpkg allparser.cmx main.ml -o main

t: t.ml
	ocamlfind ocamlc -package batteries -package batteries.syntax -syntax camlp4o -linkpkg t.ml -o t

