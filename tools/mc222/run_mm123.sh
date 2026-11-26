#!/usr/bin/env bash
# <1,2,3> (1x2 times 2x3 over F2): reproduce MC = 6 by both methods.  Separate from run_all.sh.
# Usage: ./run_mm123.sh [ext_dir]   (ext_dir as for run_all.sh; CaDiCaL rel-2.1.3 and lrat-check
# must already be built there, e.g. by run_all.sh)
set -euo pipefail
cd "$(dirname "$0")"
EXT=${1:-$PWD/ext}
CAD=$EXT/cadical-2.1.3/build/cadical
CHK=$EXT/drat-trim/lrat-check
mkdir -p out/sat
cargo build --release
B=target/release/mc222

echo "== (A) exact search"
$B mm123 4 | grep -E "symmetry|RESULT"
$B mm123 4 --no-orbits | grep -E "SUMMARY|RESULT"
$B mm123 5 --threads 4 --out out/circuit_mm123_5.txt > out/mm123_k5_orbits.log
tail -2 out/mm123_k5_orbits.log
$B mm123 6 --prefix "1,4;1,8" --out out/circuit_mm123_6_p2.txt | grep FOUND
python3 verify_circuit.py out/circuit_mm123_6_p2.txt

echo "== orbit representatives: Python vs Rust"
python3 orbits_mm123.py
grep "^root" out/mm123_k5_orbits.log | sort -k2 -n | sed -E 's/.*plane \(([0-9]+),([0-9]+)\).*/\1 \2/' > out/mm123_rust_reps.txt
cut -d' ' -f1,2 plane_orbits_mm123.txt | diff - out/mm123_rust_reps.txt && echo "same 51 representatives"

echo "== (B) SAT: plain k=4, and a k=6 circuit decoded from a cube"
python3 gen_cnf.py mm123 4 > out/sat/m4.cnf; $CAD -q out/sat/m4.cnf > out/sat/m4.out || true; head -1 out/sat/m4.out
python3 gen_cnf.py mm123 6 --helpers 0,1,2 > out/sat/m6.cnf; $CAD -q out/sat/m6.cnf > out/sat/m6.out || true; head -1 out/sat/m6.out
python3 gen_cnf.py mm123 6 --helpers 0,1,2 --decode out/sat/m6.out > out/sat/mm123_6_circ.txt
python3 verify_circuit.py out/sat/mm123_6_circ.txt

echo "== (B) SAT + LRAT over all cubes, k=4 (51 x 4) and k=5 (51 x 10)"
python3 run_sat_mm123.py "$CAD" "$CHK" 3 4 > out/run_sat_mm123_k4.log; tail -3 out/run_sat_mm123_k4.log
python3 run_sat_mm123.py "$CAD" "$CHK" 3 5 > out/run_sat_mm123_k5.log; tail -3 out/run_sat_mm123_k5.log
echo "compare out/sat_mm123_k5/results.tsv with results/sat_mm123_k5_results.tsv (columns 1-6, 9-12)"
