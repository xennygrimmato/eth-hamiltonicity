#!/bin/bash
# unconstrained three-merge ALS runs at N0 = 2 (mu = 0) and planted controls
cd "$(dirname "$0")"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
run() { python3 als3.py "$@" ; }
( run r224+c224+d224 4 400 11 0 planted > als_planted_r224c224d224.out
  run r222+c222+d222+r222+c222+d222 4 400 12 0 planted > als_planted_2x222.out
  run r222+c222+d222 20 400 1 0 > als_r222c222d222.out ) &
( run r224+c224+d224 20 400 2 0 > als_r224c224d224.out
  run r242+c242+d242 10 400 7 0 > als_r242c242d242.out ) &
( run r244+c244+d244 20 400 3 0 > als_r244c244d244.out
  run r333+c333+d333 15 400 5 0 > als_r333c333d333.out ) &
( run r444+c444+d444 20 400 4 0 > als_r444c444d444.out
  run r222+c222+d222+r222+c222+d222 20 400 6 0 > als_2x222.out ) &
wait
