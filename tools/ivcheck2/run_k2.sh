#!/usr/bin/env bash
# Independent re-check of the K_{2,3} hard-region certificates (ivcert/run_k2.sh): see README.md §k2.
set -euo pipefail
cd "$(dirname "$0")"
C=${CERTS:-../ivcert/certs/k2}
J=${JOBS:-4}
mkdir -p results
python3 selftest_k2.py | tee results/selftest_k2.log
python3 check.py --jobs "$J" --json results/k2_s910.json "$C"/s910_*.cert | tee results/k2_s910.log
python3 k2cover.py 9/10 6/5 results/k2_s910.json | tee -a results/k2_s910.log
python3 check.py --jobs "$J" --json results/k2_cl0.json "$C"/cl0_*.cert | tee results/k2_cl0.log
python3 k2cover.py 12/13 15/13 results/k2_cl0.json | tee -a results/k2_cl0.log
sha256sum "$C"/*.cert | tee results/k2_sha256.txt
