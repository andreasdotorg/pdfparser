%.vo: %.v
	coqc $<

all: pdfparser.vo

parser.vo: SfLib.vo sublist.vo
pdftype.vo: SfLib.vo
sublist.vo: SfLib.vo
pdfparser.vo : SfLib.vo parser.vo pdftype.vo

clean:
	-rm *.vo *.glob *~