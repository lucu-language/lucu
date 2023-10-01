#!/usr/bin/env bash
gcc lib.c -O3 -fno-stack-protector -nostdlib -c -o lib.o
ld lib.o out.o -o out
strip out
