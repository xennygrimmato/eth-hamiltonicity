#!/bin/bash
# second batch: larger classes (all seven flattening ranks)
cd "$(dirname "$0")"
export NUMBA_NUM_THREADS=4
for c in "3 28 3 28" "2 22 2 22" "2 20 3 28" "1 60 1 60"; do
  f=out/r_$(echo $c | tr ' ' '_').txt
  [ -s $f ] || python3 psi_build.py $c > $f 2>&1
done
