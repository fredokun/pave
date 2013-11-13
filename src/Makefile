TARGS=stests pave my_test

FLAGS=-w Ae
DEBUG=-annot

all: $(TARGS)

%.cmo:%.ml
	ocamlc $(DEBUG) $(FLAGS) -c $< 

%.cmi:%.mli
	ocamlc $(DEBUG) $(FLAGS) -c $< 

%.ml: %.mll
	ocamllex $<

%.ml: %.mly
	ocamlyacc $<

stests: utils.cmo syntax.cmo normalize.cmo norm_tests.cmo stests.cmo
	ocamlc -o $@ $^

pave: utils.cmo syntax.cmo presyntax.cmo normalize.cmo semop.cmo minim.cmo control.cmo formula.cmo parser.cmo lexer.cmo pave.cmo
	ocamlc -o $@ $^ -linkall

my_test: utils.cmo syntax.cmo presyntax.cmo normalize.cmo semop.cmo minim.cmo control.cmo formula.cmo parser.cmo lexer.cmo local_checker.cmo my_test.cmo
	ocamlc -o $@ $^

clean:
	rm -f *~ *.dot *.dot.pdf *.png $(TARGS) my_test *.cm[dtoi]* *.annot
	rm -f lexer.ml parser.ml parser.mli

.PHONY: all clean

run: my_test
	./my_test

parser.ml: formula.cmo parser.mly
lexer.ml: lexer.mll

control.cmo : utils.cmo syntax.cmo semop.cmo presyntax.cmo normalize.cmo \
    minim.cmo
formula.cmo : utils.cmo presyntax.cmo
lexer.cmo : parser.cmi
local_checker.cmo : syntax.cmo presyntax.cmo formula.cmo
minim.cmo : utils.cmo semop.cmo normalize.cmo
my_test.cmo : syntax.cmo presyntax.cmo local_checker.cmo formula.cmo
normalize.cmo : utils.cmo syntax.cmo
norm_tests.cmo : utils.cmo syntax.cmo normalize.cmo
parser.cmo : utils.cmo presyntax.cmo formula.cmo control.cmo parser.cmi
parser.cmi : parser.mli
pave.cmo : utils.cmo parser.cmi lexer.cmo control.cmo
presyntax.cmo : utils.cmo syntax.cmo
semop.cmo : utils.cmo syntax.cmo normalize.cmo
stests.cmo : utils.cmo syntax.cmo normalize.cmo norm_tests.cmo
syntax.cmo : utils.cmo
utils.cmo :

