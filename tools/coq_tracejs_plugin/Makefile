MODULES :=  src/tracejs.ml4 src/Tracejs.v test/Tests.v
NAME := Tracejs
.PHONY: all plugin clean

all: plugin src/LibTactics.vo

plugin: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(MODULES)
	coq_makefile -R src $(NAME) $(MODULES) -o Makefile.coq

%.vo %.glob: %.v
	coqc -R src $(NAME) -I ../../lib/tlc $<

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f src/LibTactics.vo src/LibTactics.glob
	rm -f Makefile.coq .depend
