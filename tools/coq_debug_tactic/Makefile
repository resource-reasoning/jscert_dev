MODULES :=  src/debug.ml4 src/Debug.v test/Tests.v
NAME := Debug
ROOT := ./
.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(MODULES)
	coq_makefile -R $(ROOT)/src $(NAME) \
		     $(MODULES) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
