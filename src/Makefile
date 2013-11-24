SRCS = $(wildcard *.ml *.mli *.mll *.mly)
TARGS = stests pave
KIND = native # d.byte
FLAGS = -w,Ae,-annot#,-warn-error,A

all: $(TARGS)

stests: _build/stests.$(KIND)
	cp $< $@

pave: _build/pave.$(KIND)
	cp $< $@

tests: _build/tests.$(KIND)
	cp $< $@

%.dot.pdf: %.dot
	dot -Tpdf $< > $@

_build/%.$(KIND): $(SRCS)
	ocamlbuild -cflags $(FLAGS) -no-links $*.$(KIND)

clean:
	@ocamlbuild -clean
	@rm -f *~ *.dot *.dot.pdf *.png $(TARGS)

.PHONY: all clean