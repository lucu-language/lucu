#!/usr/bin/env bash
ld "$1.o" -o "$1"
strip "$1"
