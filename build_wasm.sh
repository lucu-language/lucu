#!/bin/sh
./build.sh
odin build src -target:js_wasm32 -out:public/luc2.wasm -o:size
