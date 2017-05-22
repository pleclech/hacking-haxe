#!/bin/sh
if [ ! -f "src/syntax/parser.ml" -o "src/syntax/parser.mly" -nt "src/syntax/parser.ml" ]; then
	camlp4o -impl src/syntax/parser.mly -o src/syntax/parser.ml
fi

if [ "$1" -eq "0" -a ! -f "src/compiler/version.ml" ]; then
	echo let version_extra = None > src/compiler/version.ml
fi