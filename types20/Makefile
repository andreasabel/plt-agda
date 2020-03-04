# Makefile for contnorm

destdir=$(HOME)/public_html

# commands
bibtool=bibtool -- 'preserve.key.case = ON' \
	  -- 'check.double = ON' \
	  -- 'check.double.delete = ON' \
	  -- 'delete.field = { abstract }' \
	  -- 'delete.field = { dvi }' \
	  -- 'delete.field = { postscript }' \
	  -- 'delete.field = { pdf }' \
	  -- 'delete.field = { month }' \
	  -- 'delete.field = { isbn }' \
	  -- 'delete.field = { doi }'

deletemore =
# deletemore = \
#   -- 'delete.field = { editor }' \
#   -- 'delete.field = { pages }'

catcfg=sed -e "s/%.*//g" <
latex=latex
pdflatex=pdflatex
bibliography=medium.bib
sedfile=postprocess.sed
# stylefile=latex/agda.sty
files=macros.tex
# stdlib=$(HOME)/agda/test
types20tex=types20.tex
typesbibliography=all.bib
# typesbibliography=short.bib

default : types20.pdf # talkTYPES20.pdf talkTYPES20-with-notes.pdf talkTYPES20.zip

all : default ship

ship : $(destdir)/types20.pdf

$(destdir)/types20.pdf : types20.pdf
	cp -p $< $@

shipTalk : $(destdir)/talkTYPES2020.pdf

$(destdir)/talkTYPES2020.pdf : talkTYPES2020.pdf
	cp -p $< $@

#$(destdir)/types20.lagda : types20.lagda
#	cp -p $< $@

pack : types20.zip

types20.zip : types20.tex types20.bbl easychair.cls macros.tex auto-types20.bib
	zip $@ $^

talkTYPES20.zip : Makefile talkTYPES20.tex talkTYPES20.pdf talkTYPES20-with-notes.tex talkTYPES20-with-notes.pdf
	zip $@ $^

# types20
##################################################################

# types20.tex : latex/types20.tex $(sedfile)
# 	sed --file=$(sedfile) < $< > $@

# latex/types20.tex : types20.lagda
#	agda --latex -i. -i$(stdlib) $<

# types20.pdf : types20.lagda
#	pdflatex $<

# initially, run latex once to create an .aux file
# mark .aux file as fresh by creating a stamp _aux
auto-types20.aux : $(types20tex) $(files) Makefile
	$(pdflatex) $(types20tex);
	cp types20.aux $@;

# then, run bibtex
auto-types20.bbl : auto-types20.aux auto-types20.bib
	-bibtex auto-types20;

types20.bbl : auto-types20.bbl
	sed -e 's/volume/vol\./g' -e 's/URL //g' < $< > $@

# finally, finish by running latex twice again
# this will update .aux, but leave the stamp _aux intact
# (otherwise we would not converge and make would never
# return a "Nothing to do")
types20.pdf : types20.bbl
	$(pdflatex) $(types20tex);
	$(pdflatex) $(types20tex);

# auto-types20.bib is only defined if bibtool is present and all.bib exists

ifneq ($(shell which bibtool),)
ifneq ($(shell ls $(typesbibliography)),)
auto-types20.bib : auto-types20.aux $(typesbibliography)
	echo "%%%% WARNING! AUTOMATICALLY CREATED BIBFILE" > $@;
	echo "%%%% DO NOT EDIT! ALL CHANGES WILL BE LOST!" >> $@ ;
	echo "" >> $@ ;
	$(bibtool) $(deletemore) -x types20.aux -i $(typesbibliography) >> $@;
endif
endif

# Templates (reverted back to simple templates)


talk% : talk%.pdf
	cp -p $? $(destdir)/;
	touch $@;

talk%.pdf : talk%.tex
	pdflatex $<;

# cleaning

clean :
	-rm *.log *.aux *.blg *.out *_aux *.bbl

veryclean : clean
	-rm auto-*

# EOF
