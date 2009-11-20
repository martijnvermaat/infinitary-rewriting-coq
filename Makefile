# Based on the Makefile from the CoLoR library by Frederic Blanqui and
# as such governed by the CeCILL license, found at http://www.cecill.info/
#
# Martijn Vermaat, 2009-11-20

MAKEFLAGS := -r -j

.SUFFIXES:

.PHONY: clean clean-all clean-doc default config create_Makefile.coq create_Makefile.all doc tags all

COQC := $(COQBIN)coqc

MAKECOQ := $(MAKE) -f Makefile.coq
MAKEALL := $(MAKE) -f Makefile.all

VFILES := $(shell find . -name \*.v)

PROJECT := ITR

default: Makefile.coq
	$(MAKECOQ) OTHERFLAGS="-dont-load-proofs"

all: Makefile.all
	time -f %e $(MAKEALL) OTHERFLAGS="-dont-load-proofs"

config: create_Makefile.coq create_Makefile.all

create_Makefile.coq Makefile.coq:
#	coq_makefile -R . $(PROJECT) $(VFILES) > Makefile.coq
	coq_makefile $(VFILES) > Makefile.coq
	$(MAKECOQ) depend

create_Makefile.all Makefile.all:
#	coq_makefile -R . $(PROJECT) $(VFILES) $(PC_VFILE) > Makefile.all
	coq_makefile $(VFILES) $(PC_VFILE) > Makefile.all
	$(MAKEALL) depend

clean:
#	rm -f `find . -name \*~`
	$(MAKEALL) clean

clean-all: clean
	rm -f Makefile.coq Makefile.all

clean-doc:
#	rm -f doc/$(PROJECT).*.html doc/index.html
	rm -f doc/*.html

tags:
	coqtags `find . -name \*.v`

doc:
#	coqdoc --html -g -d doc -R . $(PROJECT) $(VFILES)
	coqdoc --html -g -d doc $(VFILES)
#	./createIndex

%.vo: %.v
	$(MAKECOQ) OTHERFLAGS="-dont-load-proofs" $@

%:
	$(MAKECOQ) OTHERFLAGS="-dont-load-proofs" $@
