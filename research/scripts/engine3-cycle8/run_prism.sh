#!/bin/bash
# part (c): prism ALS, 2 and 3 terms, uniform and mixed bonds (bonds listed for pairs (01,02,12) of each merge); control d=8
cd "$(dirname "$0")"
for m in prism_2_2_2 prism_4_4_4 prism_2_2_4 prism_2_4_4 prism_2_2_2_3 prism_4_4_4_3 prism_2_2_4_3 prism_2_4_4_3 prism_8_8_8; do
  python3 -u als_runs.py $m 6 150 7 > als_prism_$m.out 2>&1
done
