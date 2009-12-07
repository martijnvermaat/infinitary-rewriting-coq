# Usage: just type 'make'
#
# After adding or removing Coq files, type 'make config'.

MAKEFLAGS := -r -j

.SUFFIXES:

.PHONY: default config doc clean clean-doc

COQC := $(COQBIN)coqc

MAKECOQ := $(MAKE) -f Makefile.coq

VFILES := $(shell find . -name \*.v)

default: Makefile.coq
	$(MAKECOQ) OTHERFLAGS="-dont-load-proofs"

config Makefile.coq:
	coq_makefile -I . $(VFILES) -no-install > Makefile.coq
	$(MAKECOQ) depend

doc:
	coqdoc --html -g -d doc $(VFILES)

clean: Makefile.coq
	$(MAKECOQ) clean
	rm -f Makefile.coq

clean-doc:
	rm -f doc/*.html

%.vo: %.v
	$(MAKECOQ) OTHERFLAGS="-dont-load-proofs" $@

%:
	$(MAKECOQ) OTHERFLAGS="-dont-load-proofs" $@
