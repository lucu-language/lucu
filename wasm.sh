#!/usr/bin/env sh
cargo run -- $1 --target wasm32
node examples/wasm/hello.js out.wasm
