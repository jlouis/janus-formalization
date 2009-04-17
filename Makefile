MODULES := BaseLib Memory ZStore Janus0 Janus1 #Word32 MemMonad Janus
VS      := $(MODULES:%=%.v)

GLOBALS := .coq_globals

all: coq

coq: Makefile.coq
	make -f Makefile.coq

.PHONY: all coq clean doc

Makefile.coq: Makefile $(VS)
	coq_makefile $(VS) \
		COQC = "coqc -dump-glob $(GLOBALS)" \
		-o Makefile.coq

#Compile.ml: ImpCompile.vo
#	coqc -impredicative-set Extract >Compile.ml

clean: Makefile.coq
	make -f Makefile.coq clean
	rm -f Makefile.coq .depend

doc:
	coqdoc -d ../doc/html/coqdoc --glob-from $(GLOBALS) $(VS)
