MAKE   := $(shell which make)
COQ_MF := $(shell which coq_makefile)

all: Makefile.coq
	@$(MAKE) -f $<

Makefile.coq: _CoqProject
	@$(COQ_MF) -f $< -o $@

clean: Makefile.coq
	@$(MAKE) -f $< clean
	@rm Makefile.coq Makefile.coq.conf
	@find . -name ".*.aux" -delete
	@find . -name ".*.d" -delete

.PHONY: all clean
