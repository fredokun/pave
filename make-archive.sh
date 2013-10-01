#! /bin/sh

TOPFILES="LICENSE.txt AUTHORS VERSION Makefile"

SRCFILES="src/Makefile src/Utils.ml src/Lexer.mll src/Parser.mly src/Syntax.ml src/Normalize.ml src/Minim.ml src/Semop.ml src/Control.ml src/Presyntax.ml src/Formula.ml src/Pave.ml src/NormTests.ml src/STests.ml src/examples/*.ccs"

DATE=$(date "+%d-%m-%Y")
echo "v.${DATE}" > ./VERSION

echo "Bundle archive in pave-${DATE}/"
mkdir -p "pave-${DATE}/src"
cp -f $TOPFILES "pave-${DATE}/"
cp -f $SRCFILES "pave-${DATE}/src"

echo "Make archive: pave-${DATE}.tar.gz"
tar czf "pave-${DATE}.tar.gz" "pave-${DATE}/"

echo "Cleaning up"
rm -rf "pave-${DATE}/"




