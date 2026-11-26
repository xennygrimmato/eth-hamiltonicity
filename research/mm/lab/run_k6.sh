#!/bin/bash
# Resume the unrestricted 2x2 (over F2) k=6 multiplicative-complexity search.
# Orbits 0,1,2 of plane_orbits.json (planes (6,11),(1,2),(1,4)) are already refuted.
# The remaining 69 orbit representatives are split over k6_rem0.txt..k6_rem2.txt (one "l1 l2" per line).
# Usage: bash run_k6.sh          (runs 3 background jobs, ~1.8 h total wall time on 3 cores, ~1 GB RAM each)
# Verdict:  grep -h "k=6" k6_out*.txt
#   all three say "NO CIRCUIT"  -> no 6-AND circuit: unrestricted MC(2x2 over F2) = 7 (with k=5 refuted earlier).
#   any says "CIRCUIT EXISTS"   -> a 6-AND circuit exists (the orbit is named in the matching k6_log*.txt line "FOUND").
# Progress: k6_log<c>.txt gets one line per orbit: "orbit <i> (l1,l2): none|FOUND  states so far <N>".
cd "$(dirname "$0")"
gcc -O2 -march=native -o mc_span_bin mc_span.c || exit 1
for c in 0 1 2; do
  nohup ./mc_span_bin mm222 6 k6_rem$c.txt > k6_out$c.txt 2> k6_log$c.txt &
done
echo "started 3 jobs; check: grep -h 'k=6' k6_out*.txt ; tail -n1 k6_log*.txt"
