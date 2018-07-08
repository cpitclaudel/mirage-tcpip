#!/usr/bin/env bash
SRC=/home/clement/documents/mit/plv/fiat/src/Narcissus/Examples/NetworkStack
DST=/build/mirage-popl-2018/mirage-tcpip/src/fiat4mirage
for name in ArrayVector.ml Int64Word.ml Fiat4Mirage.ml Fiat4Mirage.mli; do
    cp "$SRC/$name" "$DST/$name"
    chmod a-w "$DST/$name"
done
