# Based on the Makefile from the CoLoR library by Frederic Blanqui and
# as such governed by the CeCILL license, found at http://www.cecill.info/
#
# Martijn Vermaat, 2009-11-20

MAKEFLAGS := -r -j

.SUFFIXES:

.PHONY: clean clean-all clean-doc default config create_Makefile.coq doc tags all

COQC := $(COQBIN)coqc

MAKECOQ := $(MAKE) -f Makefile.coq

VFILES := $(shell find . -name \*.v)

PROJECT := ITR

default: Makefile.coq
	$(MAKECOQ) OTHERFLAGS="-dont-load-proofs"

all: Makefile.coq
	$(MAKECOQ) OTHERFLAGS="-dont-load-proofs"

config: create_Makefile.coq

create_Makefile.coq Makefile.coq:
#	coq_makefile -R . $(PROJECT) $(VFILES) -no-install > Makefile.coq
	coq_makefile -I . $(VFILES) -no-install > Makefile.coq
	$(MAKECOQ) depend

clean:
#	rm -f `find . -name \*~`
	$(MAKECOQ) clean

clean-all: clean
	rm -f Makefile.coq

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
