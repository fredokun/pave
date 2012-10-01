#! /bin/sh

FILES="LICENSE.txt AUTHORS VERSION src/Makefile src/Utils.ml src/Lexer.mll src/Parser.mly src/Syntax.ml src/Normalize.ml src/Minim.ml src/Semop.ml src/Control.ml src/Presyntax.ml src/Pave.ml src/NormTests.ml src/STests.ml src/examples/*.ccs"

DATE=$(date "+%d-%m-%Y")
echo "v.${DATE}" > ./VERSION

echo "Make archive: pave-${DATE}.tar.gz"
tar cvzf "pave-${DATE}.tar.gz" $FILES




