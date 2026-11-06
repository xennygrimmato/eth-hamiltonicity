#!/bin/bash
# coupled three-merge ALS (finite-trade candidates at N0 = 2) and longer controls; waits for batch 1
cd "$(dirname "$0")"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
while pgrep -f run_batch1.sh > /dev/null; do sleep 20; done
S6='r222/c444/d444+c222/r444/d444+d222/r444/c444+r222/c444/d444+c222/r444/d444+d222/r444/c444'
( python3 als3.py "$S6" 3 400 21 10 plantedgen > als_coupled6_plantedgen.out
  python3 als3.py "$S6" 10 400 22 10 > als_coupled6_444.out ) &
( python3 als3.py r224+c224+d224 6 1500 31 0 planted > als_planted_r224c224d224_long.out
  python3 als3.py r444+c444+d444 6 1500 32 0 > als_r444c444d444_long.out ) &
( python3 als3.py r222+c222+d222+r222+c222+d222 6 1500 33 0 > als_2x222_long.out ) &
( python3 als3.py r444+c444+d444 4 1500 34 0 planted > als_planted_r444c444d444.out
  python3 als3.py r888 2 100 35 0 > als_control_f_r888.out ) &
wait
