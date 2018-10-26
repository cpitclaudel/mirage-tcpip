#!/usr/bin/env bash
SRC=/home/clement/documents/mit/plv/fiat/src/Narcissus/Examples/NetworkStack
DST=/home/clement/documents/mit/plv/mirage-popl-2018/mirage-tcpip/src/fiat4mirage
# Don't install the mli: it's broken
# Extraction bugs:
# * Extract Constant […] doesn't work for Nat.[…]
# * The Nat interface in the mli has too many fields
# * The name int clashes with int in decimal, and it gets pulled in by Nat
for name in ArrayVector.ml OCamlNativeInt.ml Int64Word.ml Fiat4Mirage.ml; do
    rm -f "$DST/$name"
    cp "$SRC/$name" "$DST/$name"
    chmod a-w "$DST/$name"
done
