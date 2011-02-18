%.vo: %.v
	coqc $<

parser.vo: SfLib.vo sublist.vo
pdftype.vo: SfLib.vo
sublist.vo: SfLib.vo
pdfparser.vo : SfLib.vo parser.vo pdftype.vo

all: pdfparser.vo

clean:
	rm *.vo *.glob *~