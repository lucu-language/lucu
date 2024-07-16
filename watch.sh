#!/bin/sh
find src/ | entr -s './build_wasm.sh && spd-say done || spd-say error'
