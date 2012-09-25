#! /bin/sh

FILES="LICENSE.txt AUTHORS Makefile Utils.ml Lexer.mll Parser.mly Syntax.ml Normalize.ml Minim.ml Semop.ml Control.ml Pave.ml NormTests.ml STests.ml examples/*.ccs"

DATE=$(date "+%d-%m-%Y")

echo "Make archive: pave-${DATE}.tar.gz"
tar cvzf "pave-${DATE}.tar.gz" $FILES




