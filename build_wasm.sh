#!/bin/sh
echo "1. generating parser"
./build.sh
echo "2. building wasm target"
odin build src -target:js_wasm32 -out:public/luc2.wasm -o:size
