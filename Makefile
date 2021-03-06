ARCH_TARGET=final
MODULES := BaseLib Memory Word32 ZStore W32Store Janus0 Janus1
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
	coqdoc --latex --body-only --glob-from $(GLOBALS) $(VS)

build-tar-ball:
	git archive --format=zip --prefix='janus-formalization-jlouis/' ${ARCH_TARGET} \
	 > janus.zip
