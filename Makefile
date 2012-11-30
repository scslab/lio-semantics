all: lio.pdf lio.vo

lio.vo: lio.v SfLib.vo
	coqc lio.v
SfLib.vo: SfLib.v
	coqc SfLib.v
lio.v: lio.ott
	ott -i lio.ott -o lio.v

lio.pdf: lio.tex
	pdflatex lio.tex
lio.tex: lio.ott
	ott -i lio.ott -o lio.tex
clean:
	-rm *.aux
	-rm *.glob
	-rm *.log
	-rm *.pdf
	-rm *.tex
	-rm lio.v
	-rm *.vo
