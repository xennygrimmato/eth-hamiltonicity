#!/bin/bash
# first batch of rank tables
cd "$(dirname "$0")"
export NUMBA_NUM_THREADS=4
for c in "1 20 1 40" "1 30 2 16" "1 16 2 20" "2 16 2 20" "2 20 2 20" "3 24 3 24" "2 16 3 24" "1 24 3 26" "3 26 3 26" "2 18 2 22"; do
  f=out/r_$(echo $c | tr ' ' '_').txt
  [ -s $f ] || python3 psi_build.py $c > $f 2>&1
done
