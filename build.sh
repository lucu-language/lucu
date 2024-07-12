#!/bin/sh
rm -f src/parser/generated/parser.odin
parcelr LALR1 src/parser/parser.grammar src/parser/generated src/parser/parser.template
mv src/parser/generated/parser.template src/parser/generated/parser.odin
