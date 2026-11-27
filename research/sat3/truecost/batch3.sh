#!/bin/bash
# factored computation: rank(Psi_N; ad|bc) against rank PP_n (jet space of the vertex) and the stable count
cd "$(dirname "$0")"
export NUMBA_NUM_THREADS=3
for c in "1 40 1 40 21" "2 20 2 20 15" "3 26 3 26 13" "1 30 2 16 12" "2 16 3 24 10" "2 28 2 28 12" "3 30 3 30 11" "2 24 3 30 11"; do
  f=out/f_$(echo $c | tr ' ' '_').txt
  [ -s $f ] || python3 factored.py $c 2>&1 | grep -v eval > $f
done
